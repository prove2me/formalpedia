-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_296
-- name    : RealPinwheel_FiveSixths_WitnessP9_296
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:22:10.892218+00:00
-- url     : https://prove2.me/theorems/b16fedbf-6e5a-46d2-9109-4aa23344e34f
-- title:
--   Exact witness block P9_296
-- statement:
--   These exact witnesses represent words 5217 through 5265 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5217–5265; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_296_5216 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (8)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (5)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (6))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (4)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (6)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (0))) (.branch 61 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5216
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 34 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 47 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 56 (.leaf (18)) (.branch 60 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-15)) (.leaf (-23)))) (.branch 34 (.leaf (-24)) (.branch 37 (.leaf (-26)) (.leaf (-27))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (-3))) (.branch 58 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 20 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 57 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 61 (.leaf (-20)) (.leaf (-13)))),
  (.branch 60 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.leaf (-3)) (.leaf (-2))),
  (.branch 55 (.branch 51 (.branch 28 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))),
  (.branch 48 (.branch 41 (.branch 38 (.branch 36 (.leaf (-27)) (.branch 37 (.leaf (-26)) (.leaf (-25)))) (.branch 39 (.leaf (-24)) (.branch 40 (.leaf (-23)) (.leaf (-22))))) (.branch 44 (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-20)) (.leaf (-19)))) (.branch 46 (.branch 45 (.leaf (-18)) (.leaf (-17))) (.branch 47 (.leaf (-16)) (.leaf (-15)))))) (.branch 55 (.branch 51 (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5217 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (7))) (.branch 14 (.leaf (5)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (8)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (7)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (8)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (5))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (7))) (.branch 45 (.leaf (4)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (8)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (1)) (.leaf (0))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (6))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (7)) (.leaf (0))) (.branch 61 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5217
  counts := ![(.branch 29 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13)))) (.branch 40 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))) (.branch 54 (.branch 48 (.leaf (17)) (.branch 51 (.leaf (18)) (.leaf (19)))) (.branch 57 (.leaf (20)) (.branch 60 (.leaf (21)) (.leaf (22))))))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 14 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-20))) (.branch 17 (.leaf (-29)) (.leaf (-30)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 42 (.leaf (-20)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.branch 49 (.leaf (-5)) (.leaf (-6))))),
  (.branch 31 (.branch 7 (.leaf (0)) (.leaf (-13))) (.branch 55 (.leaf (-19)) (.leaf (-25)))),
  (.branch 24 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 55 (.branch 49 (.leaf (-30)) (.branch 52 (.leaf (-28)) (.leaf (-26)))) (.branch 58 (.leaf (-24)) (.branch 61 (.leaf (-22)) (.leaf (-11))))),
  (.branch 57 (.branch 54 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-16)) (.leaf (-14))))) (.branch 59 (.branch 58 (.leaf (-12)) (.leaf (-10))) (.branch 60 (.leaf (-8)) (.branch 61 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 59 (.branch 37 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-8)) (.branch 61 (.leaf (-6)) (.leaf (-4))))),
  (.branch 50 (.leaf (-6)) (.leaf (-5))),
  (.branch 58 (.branch 56 (.leaf (-25)) (.branch 57 (.leaf (-23)) (.leaf (-21)))) (.branch 60 (.branch 59 (.leaf (-19)) (.leaf (-17))) (.branch 61 (.leaf (-15)) (.leaf (-13))))),
  (.branch 39 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.branch 54 (.leaf (-2)) (.leaf (0))))),
  (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 53 (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-22)) (.leaf (-20)))) (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-16)) (.leaf (-14))))) (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_296_5218 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (7))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.leaf (5))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (3))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (8))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (5)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5218
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))) (.branch 35 (.branch 32 (.leaf (-17)) (.leaf (-22))) (.branch 53 (.leaf (-25)) (.leaf (-28))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))) (.branch 37 (.leaf (-14)) (.branch 45 (.leaf (-15)) (.leaf (-19))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))) (.branch 21 (.leaf (-18)) (.branch 27 (.leaf (-19)) (.leaf (-20))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))) (.branch 49 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 54 (.leaf (-7)) (.leaf (-9))))),
  (.branch 7 (.leaf (0)) (.branch 48 (.leaf (-41)) (.leaf (-42)))),
  (.branch 17 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-21))),
  (.branch 25 (.leaf (0)) (.leaf (-37))),
  (.branch 56 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 54 (.leaf (-28)) (.branch 58 (.leaf (-27)) (.leaf (-26)))),
  (.branch 51 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-13))))),
  (.branch 60 (.branch 59 (.leaf (-20)) (.leaf (-15))) (.branch 61 (.leaf (-10)) (.leaf (-5)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-42)) (.branch 50 (.leaf (-39)) (.leaf (-36)))) (.branch 53 (.branch 52 (.leaf (-33)) (.leaf (-30))) (.branch 54 (.leaf (-27)) (.leaf (-24))))) (.branch 58 (.branch 56 (.leaf (-21)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 39 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.branch 46 (.branch 43 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-18)) (.leaf (-17))))) (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-15))) (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))))) (.branch 56 (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-37)) (.leaf (-36))) (.branch 28 (.leaf (-35)) (.leaf (-34)))) (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-32))) (.branch 32 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-29)))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-24)) (.leaf (-23))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))))) (.branch 52 (.branch 47 (.branch 45 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5219 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (8)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (1)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (7)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (2)) (.leaf (5))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.leaf (8))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (4))) (.branch 45 (.leaf (2)) (.leaf (3)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (1)) (.leaf (3))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (8)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (4))) (.branch 61 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5219
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-30)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-18)))) (.branch 37 (.leaf (-19)) (.branch 42 (.leaf (-20)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-9)) (.leaf (-11)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))) (.branch 46 (.leaf (-13)) (.branch 54 (.leaf (-14)) (.leaf (-18))))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-15)) (.leaf (-18)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (-4))) (.branch 57 (.leaf (-6)) (.leaf (-9))))]
  high := ![(.branch 48 (.branch 40 (.branch 36 (.leaf (-30)) (.leaf (-29))) (.branch 44 (.leaf (-28)) (.leaf (-27)))) (.branch 56 (.branch 52 (.leaf (-26)) (.leaf (-25))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 60 (.leaf (-16)) (.branch 61 (.leaf (-12)) (.leaf (-8))))),
  (.branch 35 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-8)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))),
  (.branch 45 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 53 (.branch 11 (.leaf (-32)) (.branch 32 (.leaf (-31)) (.leaf (-30)))) (.branch 54 (.leaf (-27)) (.branch 55 (.leaf (-24)) (.leaf (-21))))) (.branch 59 (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-15)) (.leaf (-12)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 51 (.branch 27 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12))))) (.branch 58 (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))))]
def witnessP9_296_5220 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (7))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (1)) (.leaf (4))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (8))) (.branch 30 (.leaf (2)) (.leaf (5))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (1)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (7))) (.branch 45 (.leaf (2)) (.leaf (4)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (1)) (.leaf (4))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (3)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (8))) (.branch 61 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5220
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-30)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-18)))) (.branch 37 (.leaf (-19)) (.branch 42 (.leaf (-20)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-9)) (.leaf (-11)))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 57 (.leaf (-7)) (.leaf (-9)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))) (.branch 46 (.leaf (-13)) (.branch 54 (.leaf (-14)) (.leaf (-18))))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-18))),
  (.branch 29 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.branch 40 (.branch 36 (.leaf (-30)) (.leaf (-29))) (.branch 44 (.leaf (-28)) (.leaf (-27)))) (.branch 56 (.branch 52 (.leaf (-26)) (.leaf (-25))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 60 (.leaf (-16)) (.branch 61 (.leaf (-12)) (.leaf (-8))))),
  (.branch 35 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-8)))),
  (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5))))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))),
  (.branch 56 (.branch 53 (.branch 11 (.leaf (-32)) (.branch 32 (.leaf (-31)) (.leaf (-30)))) (.branch 54 (.leaf (-27)) (.branch 55 (.leaf (-24)) (.leaf (-21))))) (.branch 59 (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-15)) (.leaf (-12)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 48 (.branch 46 (.branch 45 (.leaf (-18)) (.leaf (-17))) (.branch 47 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-12)) (.branch 52 (.leaf (-11)) (.leaf (-10)))))) (.branch 57 (.branch 55 (.branch 54 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-6)))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_296_5221 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (4)) (.leaf (0))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (2))) (.branch 41 (.leaf (7)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (3)) (.leaf (1))) (.branch 45 (.leaf (4)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (8))) (.branch 57 (.leaf (0)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (2)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5221
  counts := ![(.branch 30 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 48 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 26 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-7)) (.branch 20 (.leaf (-8)) (.leaf (-9))))) (.branch 48 (.branch 32 (.leaf (-11)) (.branch 38 (.leaf (-13)) (.leaf (-15)))) (.branch 51 (.leaf (-16)) (.branch 57 (.leaf (-17)) (.leaf (-19)))))),
  (.branch 2 (.leaf (0)) (.branch 33 (.leaf (-16)) (.leaf (-17)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.branch 52 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-52))),
  (.branch 25 (.leaf (0)) (.leaf (-37))),
  (.branch 41 (.leaf (0)) (.leaf (-21))),
  (.branch 56 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.leaf (-19)) (.leaf (-18))),
  (.branch 55 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-12)) (.leaf (-7)))),
  (.branch 60 (.branch 53 (.leaf (-17)) (.leaf (-14))) (.branch 61 (.leaf (-10)) (.leaf (-6)))),
  (.branch 59 (.branch 51 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 54 (.leaf (-3)) (.leaf (-2))) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 23 (.branch 16 (.branch 13 (.branch 11 (.leaf (-52)) (.branch 12 (.leaf (-51)) (.leaf (-50)))) (.branch 14 (.leaf (-49)) (.branch 15 (.leaf (-48)) (.leaf (-47))))) (.branch 19 (.branch 17 (.leaf (-46)) (.branch 18 (.leaf (-45)) (.leaf (-44)))) (.branch 21 (.branch 20 (.leaf (-43)) (.leaf (-42))) (.branch 22 (.leaf (-41)) (.leaf (-40)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-39)) (.branch 25 (.leaf (-38)) (.leaf (-37)))) (.branch 27 (.leaf (-36)) (.branch 28 (.leaf (-35)) (.leaf (-34))))) (.branch 32 (.branch 30 (.leaf (-33)) (.branch 31 (.leaf (-32)) (.leaf (-31)))) (.branch 34 (.branch 33 (.leaf (-30)) (.leaf (-29))) (.branch 35 (.leaf (-28)) (.leaf (-27))))))) (.branch 49 (.branch 42 (.branch 39 (.branch 37 (.leaf (-26)) (.branch 38 (.leaf (-25)) (.leaf (-24)))) (.branch 40 (.leaf (-23)) (.branch 41 (.leaf (-22)) (.leaf (-21))))) (.branch 45 (.branch 43 (.leaf (-20)) (.branch 44 (.leaf (-19)) (.leaf (-18)))) (.branch 47 (.branch 46 (.leaf (-17)) (.leaf (-16))) (.branch 48 (.leaf (-15)) (.leaf (-14)))))) (.branch 55 (.branch 52 (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))) (.branch 53 (.leaf (-10)) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-37)) (.leaf (-36))) (.branch 28 (.leaf (-35)) (.leaf (-34)))) (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-32))) (.branch 32 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-29)))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-24)) (.leaf (-23))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))))) (.branch 52 (.branch 47 (.branch 45 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 46 (.branch 43 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-18)) (.leaf (-17))))) (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-15))) (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))))) (.branch 56 (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5222 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (5)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (7)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (5))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (2))) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (3)) (.leaf (1))) (.branch 45 (.leaf (5)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (8)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (4))) (.branch 57 (.leaf (0)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (2)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5222
  counts := ![(.branch 30 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 48 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 26 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-7)) (.branch 20 (.leaf (-8)) (.leaf (-9))))) (.branch 48 (.branch 32 (.leaf (-11)) (.branch 38 (.leaf (-13)) (.leaf (-15)))) (.branch 51 (.leaf (-16)) (.branch 57 (.leaf (-17)) (.leaf (-19)))))),
  (.branch 2 (.leaf (0)) (.branch 33 (.leaf (-16)) (.leaf (-17)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.branch 52 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-17)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-25))),
  (.branch 22 (.leaf (0)) (.leaf (-40))),
  (.branch 53 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 58 (.leaf (-19)) (.leaf (-18))),
  (.branch 55 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-12)) (.leaf (-7)))),
  (.branch 60 (.branch 53 (.leaf (-17)) (.leaf (-14))) (.branch 61 (.leaf (-10)) (.leaf (-6)))),
  (.branch 59 (.branch 51 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 38 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23)))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))) (.branch 46 (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-18)) (.leaf (-17)))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-14)))))) (.branch 55 (.branch 52 (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))) (.branch 53 (.leaf (-10)) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (-40)) (.leaf (-39))) (.branch 25 (.leaf (-38)) (.branch 26 (.leaf (-37)) (.leaf (-36))))) (.branch 29 (.branch 28 (.leaf (-35)) (.leaf (-34))) (.branch 30 (.leaf (-33)) (.branch 31 (.leaf (-32)) (.leaf (-31)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-30)) (.leaf (-29))) (.branch 35 (.leaf (-28)) (.branch 36 (.leaf (-27)) (.leaf (-26))))) (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 40 (.leaf (-23)) (.branch 41 (.leaf (-22)) (.leaf (-21))))))) (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 55 (.branch 54 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-6)))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5223 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (2))) (.branch 10 (.leaf (7)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (8)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (6)) (.leaf (3))) (.branch 26 (.leaf (5)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (7)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (5))) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (6)) (.leaf (2))) (.branch 41 (.leaf (8)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (4))) (.branch 45 (.leaf (3)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (2)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (0))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (6)) (.leaf (3))) (.branch 57 (.leaf (4)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5223
  counts := ![(.branch 28 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 59 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 54 (.leaf (-8)) (.leaf (-9)))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 12 (.leaf (-8)) (.leaf (-9)))) (.branch 48 (.branch 21 (.leaf (-10)) (.leaf (-13))) (.branch 52 (.leaf (-14)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 34 (.leaf (-11)) (.branch 40 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 36 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (-32)) (.leaf (-34)))),
  (.branch 20 (.leaf (0)) (.branch 61 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 60 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 59 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10))))),
  (.branch 54 (.branch 41 (.leaf (-13)) (.leaf (-12))) (.branch 61 (.leaf (-10)) (.leaf (-7)))),
  (.branch 58 (.branch 46 (.leaf (-20)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 19 (.branch 6 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 59 (.branch 58 (.leaf (-27)) (.leaf (-23))) (.branch 60 (.leaf (-19)) (.branch 61 (.leaf (-15)) (.leaf (-11)))))),
  (.branch 50 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-4)) (.leaf (0)))),
  (.branch 58 (.branch 56 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 53 (.branch 31 (.leaf (-34)) (.branch 52 (.leaf (-33)) (.leaf (-30)))) (.branch 54 (.leaf (-27)) (.branch 55 (.leaf (-24)) (.leaf (-21))))) (.branch 59 (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-15)) (.leaf (-12)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessP9_296_5224 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (2)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (6))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (8)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (7)))) (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (4)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (6)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (5))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (8)) (.leaf (0))) (.branch 61 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5224
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.branch 51 (.leaf (-20)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 53 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 24 (.leaf (-20)) (.leaf (-21)))),
  (.branch 30 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 54 (.leaf (-9)) (.leaf (-11)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (-1))) (.branch 61 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 45 (.branch 37 (.branch 33 (.leaf (-23)) (.leaf (-22))) (.branch 41 (.leaf (-21)) (.leaf (-20)))) (.branch 53 (.branch 49 (.leaf (-19)) (.leaf (-18))) (.branch 57 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 52 (.leaf (-21)) (.leaf (-18))) (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-10)) (.leaf (-6))))),
  (.branch 58 (.branch 42 (.leaf (-22)) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 54 (.leaf (-3)) (.leaf (-2))) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 56 (.leaf (-21)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-9)) (.leaf (-8)))) (.branch 60 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5225 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (6))) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (7))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (2)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (5))) (.branch 45 (.leaf (3)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (3))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (8))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (5)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5225
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 49 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))) (.branch 35 (.branch 32 (.leaf (-12)) (.leaf (-14))) (.branch 49 (.leaf (-16)) (.leaf (-18))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-7)) (.leaf (-8)))),
  (.branch 31 (.branch 21 (.leaf (0)) (.leaf (-1))) (.branch 52 (.leaf (-3)) (.leaf (-4)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 54 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-21)) (.leaf (-22)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-22))),
  (.branch 25 (.leaf (0)) (.leaf (-37))),
  (.branch 56 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-18)) (.leaf (-17))) (.branch 58 (.leaf (-16)) (.leaf (-15)))),
  (.branch 56 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 53 (.leaf (-4)) (.branch 59 (.leaf (-2)) (.leaf (0)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-16))) (.branch 57 (.leaf (-14)) (.leaf (-12)))) (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-8))) (.branch 61 (.leaf (-6)) (.leaf (-4))))),
  (.branch 56 (.branch 53 (.branch 52 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-16)) (.leaf (-14))))) (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-21))) (.branch 43 (.leaf (-20)) (.branch 44 (.leaf (-19)) (.leaf (-18))))) (.branch 48 (.branch 46 (.leaf (-17)) (.branch 47 (.leaf (-16)) (.leaf (-15)))) (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))))) (.branch 56 (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-37)) (.leaf (-36))) (.branch 28 (.leaf (-35)) (.leaf (-34)))) (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-32))) (.branch 32 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-29)))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-24)) (.leaf (-23))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))))) (.branch 52 (.branch 47 (.branch 45 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5226 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (6))) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (8)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (7))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (8)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (3))) (.branch 45 (.leaf (2)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (7)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (0))) (.branch 61 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5226
  counts := ![(.branch 29 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 46 (.branch 38 (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13)))) (.branch 41 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))) (.branch 55 (.branch 49 (.leaf (17)) (.branch 52 (.leaf (18)) (.leaf (19)))) (.branch 58 (.leaf (20)) (.branch 60 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-20)) (.leaf (-23)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 50 (.leaf (-32)) (.leaf (-43)))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 34 (.leaf (-9)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-21)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-23)) (.branch 61 (.leaf (-22)) (.leaf (-11)))),
  (.branch 59 (.branch 51 (.leaf (-43)) (.branch 58 (.leaf (-42)) (.leaf (-38)))) (.branch 60 (.leaf (-34)) (.branch 61 (.leaf (-30)) (.leaf (-26))))),
  (.leaf (-3)),
  (.branch 58 (.branch 45 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5))))),
  (.branch 56 (.branch 53 (.branch 52 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-16)) (.leaf (-14))))) (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))),
  (.branch 57 (.branch 54 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 58 (.leaf (-6)) (.leaf (-5))) (.branch 60 (.leaf (-4)) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessP9_296_5227 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (7)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.leaf (6))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (5)) (.leaf (8))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (5)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (2))) (.branch 45 (.leaf (7)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (6)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (5))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (4)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5227
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-30)))),
  (.branch 26 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 57 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 25 (.leaf (-6)) (.branch 56 (.leaf (-7)) (.leaf (-8))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 42 (.branch 5 (.leaf (0)) (.leaf (-15))) (.branch 54 (.leaf (-16)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 48 (.branch 40 (.branch 36 (.leaf (-30)) (.leaf (-29))) (.branch 44 (.leaf (-28)) (.leaf (-27)))) (.branch 56 (.branch 52 (.leaf (-26)) (.leaf (-25))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 58 (.leaf (-16)) (.leaf (-14))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-10)) (.leaf (-8))))),
  (.branch 53 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.leaf (-4)))),
  (.branch 59 (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-13)) (.leaf (-11)))) (.branch 60 (.branch 59 (.leaf (-9)) (.leaf (-7))) (.branch 61 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.leaf (-4)) (.leaf (-3))),
  (.branch 53 (.branch 49 (.branch 47 (.branch 46 (.leaf (-17)) (.leaf (-16))) (.branch 48 (.leaf (-15)) (.leaf (-14)))) (.branch 51 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 52 (.leaf (-11)) (.leaf (-10))))) (.branch 57 (.branch 55 (.branch 54 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-6)))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_296_5228 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (6))) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (7)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (4))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (8)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5228
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 46 (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 49 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-10)))) (.branch 46 (.branch 32 (.leaf (-12)) (.leaf (-14))) (.branch 49 (.leaf (-16)) (.leaf (-18))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 55 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-45))),
  (.branch 37 (.leaf (0)) (.leaf (-25))),
  (.branch 59 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-18)) (.leaf (-17))) (.branch 58 (.leaf (-16)) (.leaf (-15)))),
  (.branch 56 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 57 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-5)) (.branch 59 (.leaf (-2)) (.leaf (0))))),
  (.branch 51 (.branch 35 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-14))) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 39 (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-45)) (.leaf (-44))) (.branch 20 (.leaf (-43)) (.branch 21 (.leaf (-42)) (.leaf (-41))))) (.branch 25 (.branch 23 (.leaf (-40)) (.branch 24 (.leaf (-39)) (.leaf (-38)))) (.branch 26 (.leaf (-37)) (.branch 27 (.leaf (-36)) (.leaf (-35)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-34)) (.leaf (-33))) (.branch 31 (.leaf (-32)) (.branch 32 (.leaf (-31)) (.leaf (-30))))) (.branch 36 (.branch 34 (.leaf (-29)) (.branch 35 (.leaf (-28)) (.leaf (-27)))) (.branch 37 (.leaf (-26)) (.branch 38 (.leaf (-25)) (.leaf (-24))))))) (.branch 50 (.branch 44 (.branch 41 (.branch 40 (.leaf (-23)) (.leaf (-22))) (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-20)) (.leaf (-19))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 48 (.leaf (-15)) (.branch 49 (.leaf (-14)) (.leaf (-13)))))) (.branch 56 (.branch 53 (.branch 51 (.leaf (-12)) (.branch 52 (.leaf (-11)) (.leaf (-10)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 38 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23)))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))) (.branch 46 (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-18)) (.leaf (-17)))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-14)))))) (.branch 55 (.branch 52 (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))) (.branch 53 (.leaf (-10)) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5229 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (6))) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (7))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (8)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (7))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (4)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5229
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 46 (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 49 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-10)))) (.branch 46 (.branch 32 (.leaf (-12)) (.leaf (-14))) (.branch 49 (.leaf (-16)) (.leaf (-18))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 55 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 23 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-18)) (.leaf (-17))) (.branch 58 (.leaf (-16)) (.leaf (-15)))),
  (.branch 56 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 57 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-5)) (.branch 59 (.leaf (-2)) (.leaf (0))))),
  (.branch 55 (.branch 52 (.branch 35 (.leaf (-25)) (.branch 51 (.leaf (-24)) (.leaf (-22)))) (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-18)) (.leaf (-16))))) (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 59 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-7))) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 44 (.branch 41 (.branch 40 (.leaf (-23)) (.leaf (-22))) (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-20)) (.leaf (-19))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 48 (.leaf (-15)) (.branch 49 (.leaf (-14)) (.leaf (-13)))))) (.branch 56 (.branch 53 (.branch 51 (.leaf (-12)) (.branch 52 (.leaf (-11)) (.leaf (-10)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_296_5230 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (8)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (7)))) (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (5)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (6)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (8)) (.leaf (0))) (.branch 61 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5230
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.branch 51 (.leaf (-20)) (.leaf (-21))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-2)) (.branch 54 (.leaf (-6)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 53 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-50)) (.leaf (-52)))),
  (.branch 14 (.leaf (0)) (.branch 55 (.leaf (-20)) (.leaf (-21)))),
  (.branch 11 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 45 (.branch 37 (.branch 33 (.leaf (-23)) (.leaf (-22))) (.branch 41 (.leaf (-21)) (.leaf (-20)))) (.branch 53 (.branch 49 (.leaf (-19)) (.leaf (-18))) (.branch 57 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 52 (.leaf (-21)) (.leaf (-18))) (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-10)) (.leaf (-6))))),
  (.branch 55 (.leaf (-9)) (.leaf (-8))),
  (.branch 58 (.branch 42 (.leaf (-22)) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 54 (.leaf (-3)) (.leaf (-2))) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 48 (.branch 46 (.branch 25 (.leaf (-52)) (.leaf (-51))) (.branch 47 (.leaf (-48)) (.leaf (-45)))) (.branch 50 (.branch 49 (.leaf (-42)) (.leaf (-39))) (.branch 51 (.leaf (-36)) (.branch 52 (.leaf (-33)) (.leaf (-30)))))) (.branch 57 (.branch 55 (.branch 54 (.leaf (-27)) (.leaf (-24))) (.branch 56 (.leaf (-21)) (.leaf (-18)))) (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-12))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 56 (.leaf (-21)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5231 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (5))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (8)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (4))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (6)))) (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (7)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (8)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (0))) (.branch 61 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5231
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.branch 51 (.leaf (-20)) (.leaf (-21))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-2)) (.branch 54 (.leaf (-6)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-50)) (.leaf (-52)))),
  (.branch 14 (.leaf (0)) (.branch 55 (.leaf (-20)) (.leaf (-21))))]
  high := ![(.branch 45 (.branch 37 (.branch 33 (.leaf (-23)) (.leaf (-22))) (.branch 41 (.leaf (-21)) (.leaf (-20)))) (.branch 53 (.branch 49 (.leaf (-19)) (.leaf (-18))) (.branch 57 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 52 (.leaf (-21)) (.leaf (-18))) (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-10)) (.leaf (-6))))),
  (.branch 55 (.leaf (-9)) (.leaf (-8))),
  (.branch 58 (.branch 42 (.leaf (-22)) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 57 (.branch 55 (.branch 54 (.leaf (-18)) (.leaf (-16))) (.branch 56 (.leaf (-14)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 60 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 53 (.branch 48 (.branch 46 (.branch 25 (.leaf (-52)) (.leaf (-51))) (.branch 47 (.leaf (-48)) (.leaf (-45)))) (.branch 50 (.branch 49 (.leaf (-42)) (.leaf (-39))) (.branch 51 (.leaf (-36)) (.branch 52 (.leaf (-33)) (.leaf (-30)))))) (.branch 57 (.branch 55 (.branch 54 (.leaf (-27)) (.leaf (-24))) (.branch 56 (.leaf (-21)) (.leaf (-18)))) (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-12))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 56 (.leaf (-21)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_296_5232 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (7))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (8)) (.leaf (4)))) (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (7)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (6))) (.branch 37 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (3)) (.leaf (8))) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (2)) (.leaf (3)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (3))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (5)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (4)))) (.branch 60 (.branch 59 (.leaf (8)) (.leaf (0))) (.branch 61 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5232
  counts := ![(.branch 29 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 29 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 32 (.leaf (-23)) (.branch 60 (.leaf (-32)) (.leaf (-36))))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-23)) (.leaf (-25)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-22)) (.leaf (-23)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-21)) (.leaf (-22)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-12)) (.leaf (-14)))),
  (.branch 18 (.leaf (0)) (.branch 59 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 61 (.leaf (-36)) (.leaf (-31))),
  (.branch 58 (.branch 49 (.leaf (-25)) (.branch 57 (.leaf (-24)) (.leaf (-20)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 46 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 51 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.branch 56 (.branch 45 (.leaf (-23)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 56 (.branch 53 (.branch 52 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-16)) (.leaf (-14))))) (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 52 (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-13)) (.leaf (-12)))) (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.leaf (-4)) (.branch 61 (.leaf (-3)) (.leaf (-2))))]
def witnessP9_296_5233 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (7)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (8)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (4)) (.leaf (6)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.leaf (5))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (4)) (.leaf (8))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (6)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (2)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (7)) (.leaf (4)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (2))) (.branch 45 (.leaf (8)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (5)) (.leaf (6)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (4))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (7))) (.branch 57 (.leaf (1)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5233
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-30)))),
  (.branch 26 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 57 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-10)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 42 (.branch 5 (.leaf (0)) (.leaf (-15))) (.branch 54 (.leaf (-16)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 48 (.branch 40 (.branch 36 (.leaf (-30)) (.leaf (-29))) (.branch 44 (.leaf (-28)) (.leaf (-27)))) (.branch 56 (.branch 52 (.leaf (-26)) (.leaf (-25))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 59 (.branch 58 (.leaf (-16)) (.leaf (-14))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-10)) (.leaf (-8))))),
  (.branch 53 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.leaf (-4)))),
  (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-13)) (.leaf (-11)))) (.branch 60 (.branch 59 (.leaf (-9)) (.leaf (-7))) (.branch 61 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.leaf (-4)) (.leaf (-3))),
  (.branch 55 (.branch 52 (.branch 35 (.leaf (-25)) (.branch 51 (.leaf (-24)) (.leaf (-22)))) (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-18)) (.leaf (-16))))) (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0))))]
def witnessP9_296_5234 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (4))) (.branch 18 (.leaf (0)) (.leaf (7)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (1)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (6)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (5)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (3))) (.branch 45 (.leaf (0)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (8)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (0))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (2))) (.branch 57 (.leaf (1)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (5))) (.branch 61 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5234
  counts := ![(.branch 27 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 49 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 9 (.leaf (-27)) (.leaf (-30)))),
  (.branch 30 (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 33 (.leaf (-5)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-5)))) (.branch 44 (.leaf (-8)) (.branch 59 (.leaf (-10)) (.leaf (-13))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-20))) (.branch 29 (.leaf (-25)) (.leaf (-27)))),
  (.branch 48 (.branch 11 (.leaf (0)) (.leaf (-5))) (.branch 60 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-28))),
  (.branch 19 (.leaf (0)) (.leaf (-43))),
  (.branch 50 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 59 (.branch 41 (.leaf (-30)) (.branch 50 (.leaf (-29)) (.leaf (-28)))) (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (-9)),
  (.branch 57 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-11)))),
  (.branch 57 (.branch 43 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 56 (.leaf (-25)) (.leaf (-22)))) (.branch 59 (.branch 58 (.leaf (-19)) (.leaf (-16))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-10)) (.leaf (-7)))))),
  (.branch 61 (.leaf (-10)) (.leaf (-7))),
  (.branch 48 (.branch 41 (.branch 37 (.branch 35 (.leaf (-28)) (.branch 36 (.leaf (-27)) (.leaf (-26)))) (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 40 (.leaf (-23)) (.leaf (-22))))) (.branch 44 (.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-20)) (.leaf (-19)))) (.branch 46 (.branch 45 (.leaf (-18)) (.leaf (-17))) (.branch 47 (.leaf (-16)) (.leaf (-15)))))) (.branch 55 (.branch 51 (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-43)) (.leaf (-42))) (.branch 22 (.leaf (-41)) (.branch 23 (.leaf (-40)) (.leaf (-39))))) (.branch 26 (.branch 25 (.leaf (-38)) (.leaf (-37))) (.branch 27 (.leaf (-36)) (.branch 28 (.leaf (-35)) (.leaf (-34)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-32))) (.branch 32 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-29))))) (.branch 37 (.branch 35 (.leaf (-28)) (.branch 36 (.leaf (-27)) (.leaf (-26)))) (.branch 38 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23))))))) (.branch 51 (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-21))) (.branch 43 (.leaf (-20)) (.branch 44 (.leaf (-19)) (.leaf (-18))))) (.branch 48 (.branch 46 (.leaf (-17)) (.branch 47 (.leaf (-16)) (.leaf (-15)))) (.branch 49 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))))) (.branch 56 (.branch 53 (.branch 52 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 53 (.branch 51 (.leaf (-12)) (.branch 52 (.leaf (-11)) (.leaf (-10)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 57 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-4)))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5235 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (2)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (8)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (5))) (.branch 18 (.leaf (4)) (.leaf (8)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (6))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (2)) (.leaf (7))) (.branch 26 (.leaf (4)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (8)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (6)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (7))) (.branch 37 (.leaf (1)) (.leaf (5))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (8)) (.leaf (2)))) (.branch 44 (.branch 43 (.leaf (6)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (7)) (.leaf (5))) (.branch 49 (.leaf (3)) (.leaf (8)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (6))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (7))) (.branch 57 (.leaf (3)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (5)) (.leaf (2))) (.branch 61 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5235
  counts := ![(.branch 27 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 32 (.leaf (-16)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-48)) (.leaf (-51)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.branch 57 (.leaf (-34)) (.leaf (-35)))),
  (.branch 26 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 43 (.leaf (-18)) (.leaf (-19)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 56 (.leaf (-13)) (.leaf (-14)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 59 (.branch 33 (.leaf (-18)) (.branch 46 (.leaf (-17)) (.leaf (-16)))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-10)) (.leaf (-7))))),
  (.branch 57 (.branch 47 (.branch 38 (.leaf (-51)) (.leaf (-50))) (.branch 56 (.leaf (-49)) (.leaf (-42)))) (.branch 59 (.branch 58 (.leaf (-35)) (.leaf (-28))) (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 34 (.branch 16 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 61 (.leaf (-14)) (.leaf (-7))))),
  (.branch 59 (.branch 58 (.leaf (-35)) (.leaf (-28))) (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7))))),
  (.branch 36 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 49 (.leaf (-11)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 55 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.leaf (-14)))) (.branch 59 (.branch 58 (.leaf (-12)) (.leaf (-10))) (.branch 60 (.leaf (-8)) (.branch 61 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 59 (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.leaf (-8)) (.branch 61 (.leaf (-6)) (.leaf (-4))))),
  (.branch 51 (.leaf (-5)) (.leaf (-4)))]
def witnessP9_296_5236 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (2)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (7))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (6)) (.leaf (0))) (.branch 18 (.leaf (8)) (.leaf (4)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (5))) (.branch 22 (.leaf (3)) (.leaf (7))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (6)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (8))) (.branch 30 (.leaf (5)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (4))) (.branch 37 (.leaf (1)) (.leaf (5))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (8)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (2)))) (.branch 44 (.branch 43 (.leaf (6)) (.leaf (7))) (.branch 45 (.leaf (4)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (8)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (6))) (.branch 53 (.leaf (4)) (.leaf (7))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (5)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (2)) (.leaf (8))) (.branch 61 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5236
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-27))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-48)) (.leaf (-52)))),
  (.branch 6 (.leaf (0)) (.branch 59 (.leaf (-20)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 53 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 38 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-22))) (.branch 23 (.leaf (-23)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 57 (.branch 41 (.branch 33 (.leaf (-27)) (.leaf (-26))) (.branch 49 (.leaf (-25)) (.leaf (-24)))) (.branch 59 (.branch 58 (.leaf (-20)) (.leaf (-16))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 57 (.branch 38 (.branch 29 (.leaf (-52)) (.leaf (-51))) (.branch 47 (.leaf (-50)) (.branch 56 (.leaf (-49)) (.leaf (-42))))) (.branch 59 (.branch 58 (.leaf (-35)) (.leaf (-28))) (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7)))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.branch 48 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.leaf (-4)) (.branch 61 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-8)) (.branch 61 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_296_5237 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (5))) (.branch 14 (.leaf (1)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (4)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (7)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (8)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (7))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (8)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (2)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (7)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (6))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (1))) (.branch 61 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5237
  counts := ![(.branch 29 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 60 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 13 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 39 (.leaf (-26)) (.leaf (-28)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 36 (.leaf (-14)) (.leaf (-17)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))) (.branch 52 (.branch 33 (.leaf (-11)) (.leaf (-12))) (.branch 58 (.leaf (-13)) (.leaf (-14))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-13))) (.branch 55 (.leaf (-14)) (.leaf (-15)))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 58 (.branch 46 (.branch 40 (.leaf (-28)) (.leaf (-27))) (.branch 52 (.leaf (-26)) (.leaf (-25)))) (.branch 60 (.branch 59 (.leaf (-21)) (.leaf (-17))) (.branch 61 (.leaf (-13)) (.leaf (-9))))),
  (.branch 49 (.branch 37 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 61 (.leaf (-13)) (.leaf (-9))))),
  (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-12))) (.branch 61 (.leaf (-10)) (.leaf (-8)))),
  (.branch 60 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 58 (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-13)) (.leaf (-11)))) (.branch 60 (.branch 59 (.leaf (-9)) (.leaf (-7))) (.branch 61 (.leaf (-5)) (.leaf (-3))))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 55 (.branch 54 (.leaf (-18)) (.leaf (-16))) (.branch 56 (.leaf (-14)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessP9_296_5238 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (8)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (5)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (7))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (2))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (3))) (.branch 41 (.leaf (0)) (.leaf (8)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (2))) (.branch 45 (.leaf (0)) (.leaf (4)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (5)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (7)) (.leaf (0))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (6)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (3))) (.branch 61 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5238
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 59 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-24)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-13)) (.leaf (-17)))) (.branch 38 (.leaf (-18)) (.branch 44 (.leaf (-19)) (.leaf (-20))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 55 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.branch 47 (.leaf (-44)) (.leaf (-45)))),
  (.branch 16 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0))]
  high := ![(.branch 55 (.branch 37 (.leaf (-27)) (.branch 46 (.leaf (-26)) (.leaf (-25)))) (.branch 60 (.leaf (-21)) (.branch 61 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.leaf (-11)) (.leaf (-7))),
  (.branch 59 (.branch 45 (.leaf (-20)) (.branch 58 (.leaf (-19)) (.leaf (-16)))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-10)) (.leaf (-7))))),
  (.branch 50 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 58 (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12)))) (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-8))) (.branch 61 (.leaf (-6)) (.leaf (-4))))),
  (.branch 54 (.branch 50 (.branch 48 (.leaf (-45)) (.branch 49 (.leaf (-42)) (.leaf (-39)))) (.branch 52 (.branch 51 (.leaf (-36)) (.leaf (-33))) (.branch 53 (.leaf (-30)) (.leaf (-27))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 59 (.branch 17 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 54 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7))))) (.branch 59 (.branch 58 (.leaf (-6)) (.leaf (-5))) (.branch 60 (.leaf (-4)) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessP9_296_5239 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (4))) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (7)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (4)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (1))) (.branch 37 (.leaf (8)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (3)) (.leaf (6))) (.branch 45 (.leaf (0)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (7)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (3)) (.leaf (0))) (.branch 57 (.leaf (8)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (6))) (.branch 61 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5239
  counts := ![(.branch 28 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 59 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 28 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))) (.branch 45 (.leaf (-8)) (.branch 56 (.leaf (-9)) (.leaf (-10))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 59 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-22)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 43 (.leaf (-4)) (.branch 55 (.leaf (-5)) (.leaf (-7))))),
  (.branch 41 (.branch 4 (.leaf (0)) (.leaf (-26))) (.branch 53 (.leaf (-29)) (.leaf (-31)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-8)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-44)) (.leaf (-46)))),
  (.branch 16 (.leaf (0)) (.branch 57 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 59 (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5))))),
  (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))),
  (.branch 59 (.branch 40 (.leaf (-22)) (.leaf (-20))) (.branch 60 (.leaf (-15)) (.branch 61 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.branch 56 (.leaf (-7)) (.leaf (-5))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-1)) (.leaf (0))))),
  (.branch 57 (.branch 55 (.branch 54 (.leaf (-31)) (.leaf (-28))) (.branch 56 (.leaf (-25)) (.leaf (-22)))) (.branch 59 (.branch 58 (.leaf (-19)) (.leaf (-16))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-10)) (.leaf (-7)))))),
  (.branch 36 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 45 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 50 (.branch 48 (.branch 27 (.leaf (-46)) (.leaf (-45))) (.branch 49 (.leaf (-42)) (.leaf (-39)))) (.branch 52 (.branch 51 (.leaf (-36)) (.leaf (-33))) (.branch 53 (.leaf (-30)) (.leaf (-27))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-12))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_296_5240 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (7)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (8)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (2)) (.leaf (1))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (2))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (8)))) (.branch 44 (.branch 43 (.leaf (3)) (.leaf (0))) (.branch 45 (.leaf (4)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (7)) (.leaf (5)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (3)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (4))) (.branch 57 (.leaf (8)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (5))) (.branch 61 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5240
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-23)) (.leaf (-27)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 38 (.leaf (-16)) (.leaf (-19)))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 61 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-20)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-3)))) (.branch 50 (.leaf (-4)) (.branch 60 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-25)) (.leaf (-26)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 56 (.branch 48 (.leaf (-27)) (.branch 52 (.leaf (-26)) (.leaf (-25)))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8))))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 39 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 60 (.leaf (-15)) (.branch 61 (.leaf (-13)) (.leaf (-11))))),
  (.leaf (-11)),
  (.branch 58 (.branch 46 (.leaf (-20)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 57 (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 55 (.leaf (-16)) (.branch 56 (.leaf (-14)) (.leaf (-12))))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 52 (.branch 50 (.leaf (-26)) (.branch 51 (.leaf (-24)) (.leaf (-22)))) (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-18)) (.leaf (-16))))) (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_296_5241 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (8))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (3)) (.leaf (2))) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (1)) (.leaf (7))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (3)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (6)))) (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (8)))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (0))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (3)) (.leaf (2))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (7))) (.branch 45 (.leaf (0)) (.leaf (5)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (3)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (1)) (.leaf (8))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (3)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (6)))) (.branch 60 (.branch 59 (.leaf (4)) (.leaf (1))) (.branch 61 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5241
  counts := ![(.branch 26 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 50 (.leaf (-24)) (.leaf (-25))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 22 (.leaf (-4)) (.branch 53 (.leaf (-8)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-23)) (.leaf (-26)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 52 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-53)) (.leaf (-55)))),
  (.branch 13 (.leaf (0)) (.branch 54 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 59 (.branch 51 (.leaf (-25)) (.branch 58 (.leaf (-22)) (.leaf (-18)))) (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-10)) (.leaf (-6))))),
  (.branch 54 (.leaf (-11)) (.branch 61 (.leaf (-10)) (.leaf (-8)))),
  (.branch 58 (.branch 49 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 57 (.leaf (-24)) (.leaf (-20)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 52 (.branch 36 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 59 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 60 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 47 (.branch 45 (.branch 24 (.leaf (-55)) (.leaf (-54))) (.branch 46 (.leaf (-51)) (.leaf (-48)))) (.branch 49 (.branch 48 (.leaf (-45)) (.leaf (-42))) (.branch 50 (.leaf (-39)) (.branch 51 (.leaf (-36)) (.leaf (-33)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-30)) (.leaf (-27))) (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-21)) (.leaf (-18))))) (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-12))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_296_5242 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (1)) (.leaf (8)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (3)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (7))) (.branch 30 (.leaf (3)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (8)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (0))) (.branch 45 (.leaf (5)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (7)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (4)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (5))) (.branch 57 (.leaf (1)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (8))) (.branch 61 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5242
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-23)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 38 (.leaf (-16)) (.leaf (-19)))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 61 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 19 (.leaf (0)) (.branch 60 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 56 (.branch 48 (.leaf (-27)) (.branch 52 (.leaf (-26)) (.leaf (-25)))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8))))),
  (.branch 59 (.branch 50 (.leaf (-21)) (.branch 58 (.leaf (-20)) (.leaf (-16)))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 39 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 60 (.leaf (-15)) (.branch 61 (.leaf (-13)) (.leaf (-11))))),
  (.leaf (-11)),
  (.branch 58 (.branch 46 (.leaf (-20)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 55 (.leaf (-16)) (.branch 56 (.leaf (-14)) (.leaf (-12))))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 56 (.branch 53 (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11)))) (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-8))))) (.branch 59 (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.leaf (-4)) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 61 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_296_5243 : CycleWitness 9 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (1)) (.leaf (6)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (8))) (.branch 22 (.leaf (3)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (3)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (7)) (.leaf (3))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (0))) (.branch 45 (.leaf (5)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (6)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (4)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (5))) (.branch 57 (.leaf (1)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (6))) (.branch 61 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5243
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-23)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 38 (.leaf (-16)) (.leaf (-19)))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 61 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-20)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-3)))) (.branch 50 (.leaf (-4)) (.branch 60 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.leaf (0)) (.leaf (-25))),
  (.branch 21 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 56 (.branch 48 (.leaf (-27)) (.branch 52 (.leaf (-26)) (.leaf (-25)))) (.branch 60 (.leaf (-24)) (.branch 61 (.leaf (-16)) (.leaf (-8))))),
  (.branch 59 (.branch 50 (.leaf (-21)) (.branch 58 (.leaf (-20)) (.leaf (-16)))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 39 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 60 (.leaf (-15)) (.branch 61 (.leaf (-13)) (.leaf (-11))))),
  (.leaf (-11)),
  (.branch 58 (.branch 46 (.leaf (-20)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 38 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23)))) (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20))))) (.branch 46 (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-18)) (.leaf (-17)))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-14)))))) (.branch 55 (.branch 52 (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-11)))) (.branch 53 (.leaf (-10)) (.branch 54 (.leaf (-9)) (.leaf (-8))))) (.branch 58 (.branch 56 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-5)))) (.branch 60 (.branch 59 (.leaf (-4)) (.leaf (-3))) (.branch 61 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6))))) (.branch 59 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5244 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 9 (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 25 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 39 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 54 (.branch 49 (.leaf (0)) (.branch 50 (.leaf (7)) (.leaf (0)))) (.branch 55 (.leaf (2)) (.branch 59 (.leaf (0)) (.leaf (8)))))))
  code := certificateP9_5244
  counts := ![(.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (7)) (.leaf (8)))) (.branch 12 (.leaf (9)) (.branch 13 (.leaf (10)) (.leaf (11)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (14)))) (.branch 19 (.leaf (15)) (.branch 21 (.leaf (16)) (.leaf (17))))) (.branch 26 (.branch 23 (.leaf (18)) (.branch 24 (.leaf (19)) (.leaf (20)))) (.branch 27 (.leaf (21)) (.branch 28 (.leaf (22)) (.leaf (23))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (24)) (.branch 32 (.leaf (25)) (.leaf (26)))) (.branch 34 (.leaf (27)) (.branch 36 (.leaf (28)) (.leaf (29))))) (.branch 41 (.branch 38 (.leaf (30)) (.branch 39 (.leaf (31)) (.leaf (32)))) (.branch 42 (.leaf (33)) (.branch 43 (.leaf (34)) (.leaf (35)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (36)) (.branch 47 (.leaf (37)) (.leaf (38)))) (.branch 49 (.leaf (39)) (.branch 51 (.leaf (40)) (.leaf (41))))) (.branch 56 (.branch 53 (.leaf (42)) (.branch 54 (.leaf (43)) (.leaf (44)))) (.branch 58 (.branch 57 (.leaf (45)) (.leaf (46))) (.branch 59 (.leaf (47)) (.leaf (48)))))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.branch 4 (.leaf (-3)) (.leaf (-4))))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-50))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.branch 50 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.leaf (-4)),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-50)) (.branch 12 (.leaf (-49)) (.leaf (-48)))) (.branch 14 (.leaf (-47)) (.branch 15 (.leaf (-46)) (.leaf (-45))))) (.branch 19 (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42)))) (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33))))) (.branch 31 (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.leaf (-26))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_296_5245 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 16 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2)))) (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 46 (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (7)) (.leaf (0)))) (.branch 56 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.branch 59 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5245
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 21 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 25 (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17)))) (.branch 26 (.leaf (18)) (.branch 28 (.leaf (19)) (.leaf (20))))))) (.branch 45 (.branch 36 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.branch 35 (.leaf (24)) (.leaf (25))))) (.branch 41 (.branch 38 (.leaf (26)) (.branch 39 (.leaf (27)) (.leaf (28)))) (.branch 42 (.leaf (29)) (.branch 43 (.leaf (30)) (.leaf (31)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (32)) (.leaf (33))) (.branch 49 (.leaf (34)) (.branch 51 (.leaf (35)) (.leaf (36))))) (.branch 56 (.branch 53 (.leaf (37)) (.branch 55 (.leaf (38)) (.leaf (39)))) (.branch 58 (.leaf (40)) (.branch 59 (.leaf (41)) (.leaf (42)))))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-50))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.branch 50 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 54 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-50)) (.branch 12 (.leaf (-49)) (.leaf (-48)))) (.branch 14 (.leaf (-47)) (.branch 15 (.leaf (-46)) (.leaf (-45))))) (.branch 19 (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42)))) (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33))))) (.branch 31 (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.leaf (-26))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_296_5246 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 16 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1)))) (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))))) (.branch 46 (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (0)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (0)))) (.branch 56 (.branch 54 (.leaf (5)) (.leaf (0))) (.branch 57 (.leaf (1)) (.branch 59 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5246
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 21 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 25 (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17)))) (.branch 26 (.leaf (18)) (.branch 28 (.leaf (19)) (.leaf (20))))))) (.branch 45 (.branch 36 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.branch 35 (.leaf (24)) (.leaf (25))))) (.branch 41 (.branch 38 (.leaf (26)) (.branch 39 (.leaf (27)) (.leaf (28)))) (.branch 42 (.leaf (29)) (.branch 43 (.leaf (30)) (.leaf (31)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (32)) (.leaf (33))) (.branch 49 (.leaf (34)) (.branch 51 (.leaf (35)) (.leaf (36))))) (.branch 56 (.branch 53 (.leaf (37)) (.branch 55 (.leaf (38)) (.leaf (39)))) (.branch 58 (.leaf (40)) (.branch 59 (.leaf (41)) (.leaf (42)))))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-6))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 54 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_296_5247 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (8))))) (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (6))))) (.branch 42 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 50 (.leaf (2)) (.branch 52 (.leaf (0)) (.leaf (7))))) (.branch 57 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.leaf (2)) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5247
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))) (.branch 24 (.branch 22 (.leaf (13)) (.leaf (14))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (18)) (.leaf (19))) (.branch 34 (.leaf (20)) (.leaf (21)))) (.branch 39 (.branch 37 (.leaf (22)) (.leaf (23))) (.branch 41 (.leaf (24)) (.branch 42 (.leaf (25)) (.leaf (26)))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (27)) (.leaf (28))) (.branch 49 (.leaf (29)) (.branch 51 (.leaf (30)) (.leaf (31))))) (.branch 56 (.branch 54 (.leaf (32)) (.leaf (33))) (.branch 57 (.leaf (34)) (.branch 59 (.leaf (35)) (.leaf (36)))))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-52))),
  (.branch 38 (.leaf (0)) (.leaf (-22))),
  (.branch 53 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-37)))]
  high := ![(.branch 58 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 34 (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-52)) (.branch 10 (.leaf (-51)) (.leaf (-50)))) (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47))))) (.branch 17 (.branch 15 (.leaf (-46)) (.branch 16 (.leaf (-45)) (.leaf (-44)))) (.branch 19 (.branch 18 (.leaf (-43)) (.leaf (-42))) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 29 (.branch 28 (.leaf (-33)) (.leaf (-32))) (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_296_5248 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (4)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5248
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-47))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 43 (.leaf (0)) (.leaf (-17))),
  (.branch 58 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-47)) (.leaf (-46))) (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43))))) (.branch 21 (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31))))) (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_296_5249 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (5)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5249
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-14))) (.branch 45 (.leaf (-16)) (.leaf (-18)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 37 (.leaf (0)) (.leaf (-23))),
  (.branch 56 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-45)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.branch 49 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.leaf (-12))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.leaf (-8)))) (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 53 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-45)) (.leaf (-44))) (.branch 18 (.leaf (-43)) (.branch 19 (.leaf (-42)) (.leaf (-41))))) (.branch 23 (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38)))) (.branch 24 (.leaf (-37)) (.branch 25 (.leaf (-36)) (.leaf (-35)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_296_5250 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (6)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (5)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (2)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5250
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 58 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_296_5251 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (8)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5251
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 20 (.leaf (0)) (.leaf (-10))),
  (.branch 28 (.leaf (0)) (.leaf (-2))),
  (.branch 24 (.leaf (0)) (.leaf (-36))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5252 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (8)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (2))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (7)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5252
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 54 (.leaf (0)) (.leaf (-6))),
  (.branch 24 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49)))) (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46))))) (.branch 18 (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43)))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_296_5253 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (6)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (7))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (5)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (8)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (7))))))))
  code := certificateP9_5253
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-14))) (.branch 45 (.leaf (-16)) (.leaf (-18)))),
  (.branch 15 (.leaf (0)) (.branch 56 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 56 (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.branch 49 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.leaf (-12))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.leaf (-8)))) (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_296_5254 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (7))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (8))) (.branch 52 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5254
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 24 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 26 (.leaf (12)) (.leaf (13)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 39 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 49 (.leaf (23)) (.leaf (24)))) (.branch 56 (.branch 54 (.leaf (25)) (.leaf (26))) (.branch 58 (.leaf (27)) (.leaf (28))))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.branch 17 (.leaf (-13)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-15)) (.leaf (-16))) (.branch 47 (.leaf (-17)) (.branch 49 (.leaf (-18)) (.leaf (-19)))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 12 (.leaf (0)) (.leaf (-18))),
  (.branch 27 (.leaf (0)) (.leaf (-3))),
  (.branch 21 (.leaf (0)) (.leaf (-39))),
  (.branch 51 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 50 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-13)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (-39)) (.leaf (-38))) (.branch 24 (.leaf (-37)) (.leaf (-36)))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5255 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (5)) (.branch 36 (.leaf (0)) (.leaf (6))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 53 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (5)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5255
  counts := ![(.branch 29 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 21 (.branch 16 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (15)) (.leaf (16))) (.branch 34 (.leaf (17)) (.leaf (18)))) (.branch 41 (.branch 39 (.leaf (19)) (.leaf (20))) (.branch 42 (.leaf (21)) (.leaf (22))))) (.branch 52 (.branch 49 (.branch 46 (.leaf (23)) (.leaf (24))) (.branch 51 (.leaf (25)) (.leaf (26)))) (.branch 56 (.branch 54 (.leaf (27)) (.leaf (28))) (.branch 59 (.leaf (29)) (.leaf (30))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 17 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 57 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5256 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (8)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5256
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-12)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-55))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 35 (.leaf (0)) (.leaf (-25))),
  (.branch 50 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 55 (.branch 53 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 18 (.branch 11 (.branch 8 (.branch 6 (.leaf (-55)) (.branch 7 (.leaf (-54)) (.leaf (-53)))) (.branch 9 (.leaf (-52)) (.branch 10 (.leaf (-51)) (.leaf (-50))))) (.branch 14 (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47)))) (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.leaf (-43)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))) (.branch 23 (.branch 22 (.leaf (-39)) (.leaf (-38))) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29))))))) (.branch 46 (.branch 39 (.branch 35 (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26)))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_296_5257 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (7))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (2))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (8))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (6)) (.leaf (2))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5257
  counts := ![(.branch 27 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 32 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 46 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-14)) (.branch 17 (.leaf (-15)) (.leaf (-19))))) (.branch 35 (.branch 32 (.leaf (-20)) (.leaf (-24))) (.branch 47 (.leaf (-25)) (.branch 50 (.leaf (-29)) (.leaf (-30)))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-2))),
  (.branch 22 (.leaf (0)) (.leaf (-38))),
  (.branch 52 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-47))),
  (.branch 43 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 58 (.branch 51 (.leaf (-30)) (.leaf (-29))) (.branch 59 (.leaf (-26)) (.leaf (-23)))),
  (.branch 52 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 57 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-38)) (.leaf (-37))) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-47)) (.leaf (-46))) (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43))))) (.branch 21 (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31))))) (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_296_5258 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (7)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (4)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (5)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_5258
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17))))) (.branch 50 (.branch 46 (.leaf (18)) (.branch 47 (.leaf (19)) (.leaf (20)))) (.branch 55 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 32 (.leaf (-19)) (.branch 47 (.leaf (-22)) (.leaf (-25))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-18))),
  (.branch 27 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 56 (.branch 48 (.leaf (-25)) (.leaf (-24))) (.branch 59 (.leaf (-22)) (.leaf (-17)))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5259 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (5))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5259
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17))))) (.branch 50 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 56 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 32 (.leaf (-17)) (.branch 50 (.leaf (-22)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 17 (.leaf (-2)) (.leaf (-4)))) (.branch 47 (.branch 42 (.leaf (-6)) (.leaf (-7))) (.branch 59 (.leaf (-9)) (.leaf (-11))))),
  (.branch 19 (.leaf (0)) (.branch 49 (.leaf (-4)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-38))),
  (.branch 52 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 51 (.leaf (-23)) (.branch 59 (.leaf (-22)) (.leaf (-17)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-11)),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-5))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-1)) (.leaf (0))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-38)) (.leaf (-37))) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5260 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (7))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (6))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (4)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (8))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (5)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5260
  counts := ![(.branch 27 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 32 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))) (.branch 32 (.leaf (-23)) (.branch 47 (.leaf (-28)) (.leaf (-33))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 23 (.leaf (0)) (.leaf (-37))),
  (.branch 53 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 58 (.branch 48 (.leaf (-33)) (.leaf (-32))) (.branch 59 (.leaf (-28)) (.leaf (-24)))),
  (.leaf (-4)),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 29 (.branch 28 (.leaf (-33)) (.leaf (-32))) (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_296_5261 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (8)) (.leaf (0)))) (.branch 35 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (4)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 52 (.leaf (0)) (.leaf (6))))) (.branch 57 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.leaf (5)) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5261
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))) (.branch 24 (.branch 22 (.leaf (13)) (.leaf (14))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (18)) (.leaf (19))) (.branch 34 (.leaf (20)) (.leaf (21)))) (.branch 39 (.branch 37 (.leaf (22)) (.leaf (23))) (.branch 41 (.leaf (24)) (.branch 42 (.leaf (25)) (.leaf (26)))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (27)) (.leaf (28))) (.branch 49 (.leaf (29)) (.branch 51 (.leaf (30)) (.leaf (31))))) (.branch 56 (.branch 54 (.leaf (32)) (.leaf (33))) (.branch 57 (.leaf (34)) (.branch 59 (.leaf (35)) (.leaf (36)))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 53 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 18 (.leaf (0)) (.leaf (-12))),
  (.branch 28 (.leaf (0)) (.leaf (-2))),
  (.branch 53 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-47))),
  (.branch 33 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 58 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-47)) (.leaf (-46))) (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43))))) (.branch 21 (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31))))) (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 39 (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_296_5262 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (7)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5262
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-49))),
  (.branch 26 (.leaf (0)) (.leaf (-34))),
  (.branch 41 (.leaf (0)) (.leaf (-19))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 55 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47)))) (.branch 15 (.leaf (-46)) (.branch 16 (.leaf (-45)) (.leaf (-44))))) (.branch 20 (.branch 18 (.leaf (-43)) (.branch 19 (.leaf (-42)) (.leaf (-41)))) (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-37)) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32))))) (.branch 32 (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))))) (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296_5263 : CycleWitness 9 where
  length := 60
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 29 (.branch 27 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (5)) (.leaf (0))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (7)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (2)) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5263
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 24 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 26 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (17)) (.leaf (18))) (.branch 35 (.leaf (19)) (.leaf (20)))) (.branch 41 (.branch 39 (.leaf (21)) (.leaf (22))) (.branch 42 (.leaf (23)) (.leaf (24))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (25)) (.leaf (26))) (.branch 49 (.leaf (27)) (.leaf (28)))) (.branch 55 (.branch 53 (.leaf (29)) (.leaf (30))) (.branch 57 (.leaf (31)) (.branch 59 (.leaf (32)) (.leaf (33)))))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))) (.branch 29 (.leaf (-12)) (.branch 49 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 54 (.branch 50 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.leaf (-11)) (.branch 58 (.leaf (-10)) (.leaf (-9))))),
  (.branch 59 (.leaf (-6)) (.leaf (-3))),
  (.branch 56 (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_296_5264 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (3))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (3))) (.branch 37 (.leaf (0)) (.leaf (7))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (5)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5264
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 24 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 26 (.leaf (12)) (.leaf (13)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 39 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 49 (.leaf (23)) (.leaf (24)))) (.branch 56 (.branch 54 (.leaf (25)) (.leaf (26))) (.branch 58 (.leaf (27)) (.leaf (28))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 57 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.branch 17 (.leaf (-13)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-15)) (.leaf (-16))) (.branch 47 (.leaf (-17)) (.branch 49 (.leaf (-18)) (.leaf (-19)))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.leaf (-42))),
  (.branch 38 (.leaf (0)) (.leaf (-22))),
  (.branch 57 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-42)) (.leaf (-41))) (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38))))) (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_296 : Fin 49 → CycleWitness 9 := ![witnessP9_296_5216, witnessP9_296_5217, witnessP9_296_5218, witnessP9_296_5219, witnessP9_296_5220, witnessP9_296_5221, witnessP9_296_5222, witnessP9_296_5223, witnessP9_296_5224, witnessP9_296_5225, witnessP9_296_5226, witnessP9_296_5227, witnessP9_296_5228, witnessP9_296_5229, witnessP9_296_5230, witnessP9_296_5231, witnessP9_296_5232, witnessP9_296_5233, witnessP9_296_5234, witnessP9_296_5235, witnessP9_296_5236, witnessP9_296_5237, witnessP9_296_5238, witnessP9_296_5239, witnessP9_296_5240, witnessP9_296_5241, witnessP9_296_5242, witnessP9_296_5243, witnessP9_296_5244, witnessP9_296_5245, witnessP9_296_5246, witnessP9_296_5247, witnessP9_296_5248, witnessP9_296_5249, witnessP9_296_5250, witnessP9_296_5251, witnessP9_296_5252, witnessP9_296_5253, witnessP9_296_5254, witnessP9_296_5255, witnessP9_296_5256, witnessP9_296_5257, witnessP9_296_5258, witnessP9_296_5259, witnessP9_296_5260, witnessP9_296_5261, witnessP9_296_5262, witnessP9_296_5263, witnessP9_296_5264]
end RealPinwheel.FiveSixths


