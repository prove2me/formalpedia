-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_198
-- name    : RealPinwheel_FiveSixths_WitnessD8_198
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:39:46.018197+00:00
-- url     : https://prove2.me/theorems/0c2a8615-95ca-454c-89db-2cfd40858c4f
-- title:
--   Exact witness block D8_198
-- statement:
--   These exact witnesses represent words 2185 through 2206 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2185–2206; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_198_2184 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (6)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (6)) (.branch 37 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2184
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (-23)) (.leaf (-24)))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 42 (.branch 38 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 25 (.leaf (-16)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))]
def witnessD8_198_2185 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (7))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (6))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (6)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2185
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 39 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 10 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.leaf (-30))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 18 (.leaf (-4)) (.branch 24 (.leaf (-6)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 36 (.leaf (-19)) (.branch 43 (.leaf (-14)) (.leaf (-7)))),
  (.branch 41 (.branch 3 (.leaf (-30)) (.branch 22 (.leaf (-29)) (.leaf (-28)))) (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-8)) (.leaf (-7))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 23 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8))))) (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_198_2186 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (4)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (5))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (7)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (4)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2186
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 10 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-33))),
  (.branch 33 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-33)) (.leaf (-32))) (.branch 14 (.leaf (-31)) (.leaf (-30)))) (.branch 17 (.branch 16 (.leaf (-29)) (.leaf (-28))) (.branch 18 (.leaf (-27)) (.leaf (-26))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-25)) (.leaf (-24))) (.branch 22 (.leaf (-23)) (.leaf (-22)))) (.branch 25 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-19)) (.leaf (-18)))))) (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 30 (.leaf (-15)) (.leaf (-14)))) (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.leaf (-10))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2187 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (6)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2187
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.leaf (0)) (.leaf (-9))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-37))),
  (.branch 29 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.branch 33 (.leaf (-14)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 25 (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-37)) (.leaf (-36))) (.branch 10 (.leaf (-35)) (.leaf (-34)))) (.branch 13 (.branch 12 (.leaf (-33)) (.leaf (-32))) (.branch 14 (.leaf (-31)) (.branch 15 (.leaf (-30)) (.leaf (-29)))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 19 (.leaf (-26)) (.leaf (-25)))) (.branch 22 (.branch 21 (.leaf (-24)) (.leaf (-23))) (.branch 23 (.leaf (-22)) (.branch 24 (.leaf (-21)) (.leaf (-20))))))) (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6))))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 32 (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2188 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (7)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (7))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (7)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (5)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2188
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-29)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-6)) (.leaf (-8))))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-25)) (.leaf (-20)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_198_2189 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (7)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (6)) (.branch 29 (.leaf (5)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (7)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2189
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (-23)) (.leaf (-24)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2190 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (7))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (3)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (7)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2190
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-10)) (.leaf (-13)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-29)) (.leaf (-30)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-13))) (.branch 24 (.leaf (-16)) (.leaf (-27)))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-11))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-7)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-25)) (.leaf (-20)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 38 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 39 (.leaf (-24)) (.leaf (-22)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.leaf (-14))))),
  (.branch 14 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))]
def witnessD8_198_2191 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (6)) (.leaf (1)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (7)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (5)) (.leaf (2))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (1)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (7)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2191
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 14 (.leaf (-11)) (.leaf (-14)))) (.branch 36 (.leaf (-16)) (.branch 40 (.leaf (-18)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-17))) (.branch 43 (.leaf (-14)) (.leaf (-11)))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.leaf (-7)))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 27 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))),
  (.branch 36 (.branch 32 (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2192 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (2)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (7))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (6)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (5)) (.leaf (7))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (3)) (.leaf (6)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2192
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-24)) (.leaf (-28)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 38 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-2)) (.leaf (0))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 40 (.branch 22 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-15))) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 35 (.leaf (-6)) (.leaf (-5))),
  (.branch 42 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9)))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2193 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (7)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (4)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_2193
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-40))),
  (.branch 26 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 40 (.leaf (-14)) (.leaf (-13))))),
  (.branch 38 (.leaf (-13)) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-5)) (.branch 40 (.leaf (-2)) (.leaf (0)))),
  (.branch 41 (.branch 33 (.leaf (-14)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-40)) (.leaf (-39))) (.branch 7 (.leaf (-38)) (.branch 8 (.leaf (-37)) (.leaf (-36))))) (.branch 11 (.branch 10 (.leaf (-35)) (.leaf (-34))) (.branch 12 (.leaf (-33)) (.branch 13 (.leaf (-32)) (.leaf (-31)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-30)) (.leaf (-29))) (.branch 17 (.leaf (-28)) (.branch 18 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 20 (.leaf (-25)) (.leaf (-24))) (.branch 22 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-21))))))) (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16))))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6))))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_198_2194 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (7)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (7)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2194
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-29)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-25)) (.leaf (-20)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_198_2195 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (7)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (5)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2195
  counts := ![(.branch 21 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 38 (.branch 36 (.leaf (14)) (.leaf (15))) (.branch 40 (.leaf (16)) (.branch 43 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-35)) (.leaf (-37)))),
  (.branch 10 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 41 (.leaf (-14)) (.leaf (-9))),
  (.branch 36 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 42 (.leaf (-6)) (.branch 43 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-37)) (.branch 33 (.leaf (-36)) (.leaf (-33)))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-27)) (.leaf (-24))))) (.branch 40 (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2196 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (0)) (.leaf (7))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (5)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (7)) (.branch 43 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2196
  counts := ![(.branch 21 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 38 (.branch 36 (.leaf (14)) (.leaf (15))) (.branch 40 (.leaf (16)) (.branch 43 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-35)) (.leaf (-37)))),
  (.branch 10 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-29)) (.leaf (-30)))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 41 (.leaf (-14)) (.leaf (-9))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 23 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-37)) (.branch 33 (.leaf (-36)) (.leaf (-33)))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-27)) (.leaf (-24))))) (.branch 40 (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-27))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-21)) (.leaf (-18))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 28 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_198_2197 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (7)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (7))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (6)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (7)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (6))))))))
  code := certificateD8_2197
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-35))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 39 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 34 (.branch 4 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-27)) (.leaf (-24))))) (.branch 40 (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_198_2198 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (6)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (7))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (5)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (2)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (0)) (.leaf (6))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_2198
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))) (.branch 34 (.branch 17 (.leaf (-6)) (.leaf (-7))) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0))]
  high := ![(.branch 33 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 23 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_198_2199 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (7)) (.branch 7 (.leaf (1)) (.leaf (5)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (7)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2199
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 22 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-29)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 40 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-25)) (.leaf (-20)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2200 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (7)) (.branch 7 (.leaf (2)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (6)) (.leaf (4))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (7)) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (6)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2200
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-6)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 32 (.leaf (-17)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 43 (.leaf (-10)) (.leaf (-9))),
  (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_198_2201 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (4)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (7))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (5)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (4)) (.leaf (7))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (2)) (.leaf (6))))))))
  code := certificateD8_2201
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-30))) (.branch 14 (.leaf (-32)) (.branch 39 (.leaf (-34)) (.leaf (-35))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-5)) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (-3)) (.leaf (-5)))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 41 (.branch 35 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-6)) (.branch 43 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 40 (.leaf (-35)) (.leaf (-28))) (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-7)))),
  (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 40 (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.branch 33 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))),
  (.branch 34 (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2202 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (7)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_2202
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-35)) (.leaf (-36)))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 14 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 40 (.leaf (-14)) (.leaf (-13))))),
  (.branch 38 (.leaf (-13)) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-5)) (.branch 40 (.leaf (-2)) (.leaf (0)))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 35 (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-33)) (.leaf (-30)))) (.branch 36 (.leaf (-27)) (.branch 37 (.leaf (-24)) (.leaf (-21))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 11 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2203 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (2)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (7)) (.branch 37 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2203
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 14 (.leaf (0)) (.leaf (-30))),
  (.branch 36 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 42 (.branch 38 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6))))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 21 (.branch 17 (.branch 15 (.leaf (-30)) (.branch 16 (.leaf (-29)) (.leaf (-28)))) (.branch 19 (.branch 18 (.leaf (-27)) (.leaf (-26))) (.branch 20 (.leaf (-25)) (.leaf (-24))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 24 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-17)) (.leaf (-16)))))) (.branch 36 (.branch 32 (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2204 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (6)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (5)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (7)) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2204
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-19)) (.leaf (-23)))),
  (.branch 35 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-7)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-35)) (.leaf (-37)))),
  (.branch 10 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 14 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 42 (.branch 38 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.leaf (-6)) (.branch 39 (.leaf (-5)) (.leaf (-4)))),
  (.branch 32 (.branch 14 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-15))) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.leaf (-11)) (.branch 43 (.leaf (-10)) (.leaf (-9)))),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-37)) (.branch 33 (.leaf (-36)) (.leaf (-33)))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-27)) (.leaf (-24))))) (.branch 40 (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_198_2205 : CycleWitness 8 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (6)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (7)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (6)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (7)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_2205
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 19 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-24)) (.leaf (-26)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 41 (.branch 31 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-20)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.branch 18 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 32 (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_198 : Fin 22 → CycleWitness 8 := ![witnessD8_198_2184, witnessD8_198_2185, witnessD8_198_2186, witnessD8_198_2187, witnessD8_198_2188, witnessD8_198_2189, witnessD8_198_2190, witnessD8_198_2191, witnessD8_198_2192, witnessD8_198_2193, witnessD8_198_2194, witnessD8_198_2195, witnessD8_198_2196, witnessD8_198_2197, witnessD8_198_2198, witnessD8_198_2199, witnessD8_198_2200, witnessD8_198_2201, witnessD8_198_2202, witnessD8_198_2203, witnessD8_198_2204, witnessD8_198_2205]
end RealPinwheel.FiveSixths


