-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_185
-- name    : RealPinwheel_FiveSixths_WitnessD8_185
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:56.532938+00:00
-- url     : https://prove2.me/theorems/bc4ab5d8-9c03-43c4-a733-9a760e5d3457
-- title:
--   Exact witness block D8_185
-- statement:
--   These exact witnesses represent words 1913 through 1932 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1913–1932; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_185_1912 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (4)) (.leaf (0)))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1))))))) (.branch 36 (.branch 29 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1912
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.branch 33 (.leaf (14)) (.leaf (15))))) (.branch 41 (.branch 37 (.leaf (16)) (.branch 39 (.leaf (17)) (.leaf (18)))) (.branch 44 (.leaf (19)) (.branch 46 (.leaf (20)) (.leaf (21))))))),
  (.branch 24 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-10))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 42 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-33))),
  (.branch 31 (.leaf (0)) (.leaf (-17))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 42 (.leaf (-10)) (.branch 47 (.leaf (-9)) (.leaf (-6)))),
  (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-4)) (.branch 44 (.leaf (-2)) (.leaf (0)))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.leaf (-30)))) (.branch 21 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.leaf (-18)))))) (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_185_1913 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (7)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1913
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 24 (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1914 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1914
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-44))),
  (.branch 28 (.leaf (0)) (.leaf (-20))),
  (.branch 40 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-32)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-44)) (.leaf (-43))) (.branch 7 (.leaf (-42)) (.branch 8 (.leaf (-41)) (.leaf (-40))))) (.branch 12 (.branch 10 (.leaf (-39)) (.branch 11 (.leaf (-38)) (.leaf (-37)))) (.branch 13 (.leaf (-36)) (.branch 14 (.leaf (-35)) (.leaf (-34)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29))))) (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 24 (.leaf (-25)) (.branch 25 (.leaf (-24)) (.leaf (-23))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 27 (.leaf (-22)) (.leaf (-21))) (.branch 29 (.leaf (-20)) (.branch 30 (.leaf (-19)) (.leaf (-18))))) (.branch 34 (.branch 32 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_185_1915 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (2)))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (7))))))) (.branch 36 (.branch 29 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (3)) (.leaf (0))))) (.branch 32 (.branch 30 (.leaf (1)) (.branch 31 (.leaf (6)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1915
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-10)) (.branch 34 (.leaf (-13)) (.leaf (-16))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-27)) (.leaf (-33)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-13)) (.leaf (-17)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 46 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-13)) (.leaf (-11)))),
  (.branch 31 (.branch 17 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.leaf (-30)))) (.branch 45 (.branch 38 (.leaf (-29)) (.leaf (-28))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 33 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 40 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_185_1916 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (7)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (6)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (7)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1916
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1917 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (7)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_1917
  counts := ![(.branch 22 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13))))) (.branch 40 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-14)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 41 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-10))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 42 (.branch 39 (.branch 21 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1918 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (6)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (7))))))) (.branch 36 (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (0))) (.branch 45 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1918
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 20 (.branch 18 (.leaf (11)) (.leaf (12))) (.branch 22 (.leaf (13)) (.leaf (14)))))) (.branch 36 (.branch 30 (.branch 26 (.branch 25 (.leaf (15)) (.leaf (16))) (.branch 28 (.leaf (17)) (.leaf (18)))) (.branch 33 (.branch 31 (.leaf (19)) (.leaf (20))) (.branch 34 (.leaf (21)) (.leaf (22))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (23)) (.leaf (24))) (.branch 41 (.leaf (25)) (.leaf (26)))) (.branch 46 (.branch 44 (.leaf (27)) (.leaf (28))) (.branch 47 (.leaf (29)) (.leaf (30))))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 43 (.leaf (-6)) (.leaf (-5))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_185_1919 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1))))))))
  code := certificateD8_1919
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 20 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.leaf (13)))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16)))) (.branch 33 (.branch 31 (.leaf (17)) (.leaf (18))) (.branch 34 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.leaf (21)) (.branch 40 (.leaf (22)) (.leaf (23)))) (.branch 45 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 47 (.leaf (26)) (.leaf (27))))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-36))),
  (.branch 28 (.leaf (0)) (.leaf (-20))),
  (.branch 44 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 44 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 46 (.leaf (-11)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.leaf (-33)))) (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1920 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (7))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1920
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_185_1921 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (7)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6)))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (7)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_1921
  counts := ![(.branch 22 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13))))) (.branch 40 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-14)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 41 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-10))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1922 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (5))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (7))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1922
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-30))),
  (.branch 42 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))) (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_185_1923 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (6)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (7)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1923
  counts := ![(.branch 22 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.branch 33 (.leaf (12)) (.leaf (13))))) (.branch 41 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 28 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 47 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-35))),
  (.branch 29 (.leaf (0)) (.leaf (-19))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 44 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.leaf (-32)))) (.branch 19 (.branch 18 (.leaf (-31)) (.leaf (-30))) (.branch 20 (.leaf (-29)) (.leaf (-28))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_185_1924 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1924
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_185_1925 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1925
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-8)))) (.branch 30 (.leaf (-10)) (.branch 42 (.leaf (-12)) (.leaf (-14))))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-38))),
  (.branch 34 (.leaf (0)) (.leaf (-14)))]
  high := ![(.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-38)) (.leaf (-37))) (.branch 13 (.leaf (-36)) (.leaf (-35)))) (.branch 16 (.branch 15 (.leaf (-34)) (.leaf (-33))) (.branch 17 (.leaf (-32)) (.branch 18 (.leaf (-31)) (.leaf (-30)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))))) (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_185_1926 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1926
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 40 (.leaf (0)) (.leaf (-8)))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_185_1927 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1927
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 28 (.leaf (-5)) (.branch 40 (.leaf (-7)) (.leaf (-9))))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-7)) (.leaf (-6)))) (.branch 46 (.branch 45 (.leaf (-5)) (.leaf (-4))) (.branch 47 (.leaf (-3)) (.leaf (-2))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 26 (.branch 22 (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27)))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.leaf (-23))))) (.branch 29 (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_185_1928 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (7))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1928
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.branch 33 (.leaf (14)) (.leaf (15))))) (.branch 42 (.branch 37 (.leaf (16)) (.branch 39 (.leaf (17)) (.leaf (18)))) (.branch 44 (.leaf (19)) (.branch 46 (.leaf (20)) (.leaf (21))))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 7 (.leaf (-13)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 40 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-7)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_185_1929 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (4)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1929
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 44 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 20 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 34 (.branch 27 (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_185_1930 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (5)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1930
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 32 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_185_1931 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1931
  counts := ![(.branch 22 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 35 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 30 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 42 (.branch 37 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 22 (.leaf (-13)) (.branch 46 (.leaf (-16)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 47 (.leaf (-18)) (.leaf (-11))),
  (.branch 46 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_185 : Fin 20 → CycleWitness 8 := ![witnessD8_185_1912, witnessD8_185_1913, witnessD8_185_1914, witnessD8_185_1915, witnessD8_185_1916, witnessD8_185_1917, witnessD8_185_1918, witnessD8_185_1919, witnessD8_185_1920, witnessD8_185_1921, witnessD8_185_1922, witnessD8_185_1923, witnessD8_185_1924, witnessD8_185_1925, witnessD8_185_1926, witnessD8_185_1927, witnessD8_185_1928, witnessD8_185_1929, witnessD8_185_1930, witnessD8_185_1931]
end RealPinwheel.FiveSixths


