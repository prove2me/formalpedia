-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_309
-- name    : RealPinwheel_FiveSixths_WitnessP9_309
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:53.541014+00:00
-- url     : https://prove2.me/theorems/b58ce321-3dd3-4751-9982-eb8899f6e5f3
-- title:
--   Exact witness block P9_309
-- statement:
--   These exact witnesses represent words 5889 through 5944 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5889–5944; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_309_5888 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (7)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (4)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (5))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (8)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5888
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 28 (.leaf (-18)) (.branch 32 (.leaf (-21)) (.leaf (-24))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 44 (.leaf (-24)) (.leaf (-31)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-32))),
  (.branch 49 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 43 (.branch 33 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 48 (.leaf (-21)) (.branch 53 (.leaf (-20)) (.leaf (-16))))),
  (.branch 51 (.branch 45 (.leaf (-31)) (.leaf (-30))) (.branch 52 (.leaf (-26)) (.branch 53 (.leaf (-22)) (.leaf (-18))))),
  (.branch 47 (.leaf (-5)) (.leaf (-4))),
  (.branch 52 (.branch 44 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.leaf (-29)))) (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.leaf (-21)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.leaf (-17)))))) (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5889 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (8)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (5)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (0)) (.leaf (8)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (5)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (8)) (.branch 42 (.leaf (6)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (1)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (0)) (.leaf (7)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5889
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 11 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 47 (.leaf (-34)) (.leaf (-35)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-8)))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 51 (.branch 39 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.leaf (-35)) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5890 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_5890
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 30 (.leaf (0)) (.leaf (-24))),
  (.branch 48 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5891 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (7)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5891
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 30 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 48 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-37))),
  (.branch 35 (.leaf (0)) (.leaf (-19))),
  (.branch 53 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20))))))) (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_309_5892 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (7))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (1))) (.branch 26 (.leaf (4)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (7))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (0)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5892
  counts := ![(.branch 23 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-4)) (.branch 34 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-40)) (.leaf (-41)))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (-12))) (.branch 52 (.leaf (-13)) (.leaf (-14)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 34 (.branch 26 (.leaf (-41)) (.leaf (-39))) (.branch 42 (.leaf (-37)) (.leaf (-35)))) (.branch 52 (.branch 51 (.leaf (-28)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 53 (.leaf (-14)) (.leaf (-7))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 33 (.leaf (-17)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_309_5893 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (8)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (4))) (.branch 26 (.leaf (7)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (8)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (4)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (4))) (.branch 53 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5893
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 43 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-16)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 41 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_309_5894 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (8)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (7)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (7)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5894
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 17 (.leaf (-12)) (.branch 44 (.leaf (-17)) (.leaf (-21))))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-10))) (.branch 43 (.leaf (-12)) (.leaf (-14)))),
  (.branch 16 (.leaf (0)) (.branch 53 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 47 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 45 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-14)) (.leaf (-11))))),
  (.branch 39 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 48 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-14)) (.leaf (-13))) (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.leaf (-4))]
def witnessP9_309_5895 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (4))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (4)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (5)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_5895
  counts := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-8)))) (.branch 39 (.leaf (-9)) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-4)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (-39)) (.leaf (-41)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 52 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 49 (.branch 47 (.branch 36 (.leaf (-41)) (.leaf (-40))) (.branch 48 (.leaf (-35)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 31 (.branch 9 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4))))))]
def witnessP9_309_5896 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (2)) (.leaf (8)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (2)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (1)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (0)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (8))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5896
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 11 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 51 (.branch 39 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.leaf (-8)) (.leaf (-5))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_309_5897 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (7)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (3))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (5)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5897
  counts := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 20 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 38 (.leaf (-10)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-46))),
  (.branch 26 (.leaf (0)) (.leaf (-28))),
  (.branch 44 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 40 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-46)) (.leaf (-45))) (.branch 11 (.leaf (-44)) (.branch 12 (.leaf (-43)) (.leaf (-42))))) (.branch 16 (.branch 14 (.leaf (-41)) (.branch 15 (.leaf (-40)) (.leaf (-39)))) (.branch 17 (.leaf (-38)) (.branch 18 (.leaf (-37)) (.leaf (-36)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 23 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30))))) (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 29 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-24))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 33 (.branch 29 (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5898 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (6)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (7)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5898
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 30 (.leaf (0)) (.leaf (-24))),
  (.branch 48 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 47 (.branch 42 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 46 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5899 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (8)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (8)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (7)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (7)) (.leaf (2))))))))
  code := certificateP9_5899
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-34)) (.leaf (-38)))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (-9)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 26 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 37 (.leaf (-36)) (.branch 48 (.leaf (-35)) (.leaf (-30))))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 42 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5900 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (8)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (7)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (8)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (7)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5900
  counts := ![(.branch 26 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 49 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 50 (.leaf (-20)) (.leaf (-16))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 14 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessP9_309_5901 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (7)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5901
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-24))),
  (.branch 12 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5902 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (7)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5902
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-24))),
  (.branch 12 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-17)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5903 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (5))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5903
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 13 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-5)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-24))),
  (.branch 17 (.leaf (0)) (.leaf (-37))),
  (.branch 44 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.leaf (-9)) (.branch 48 (.leaf (-8)) (.leaf (-5)))),
  (.branch 51 (.branch 41 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8)))) (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20))))))) (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5904 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (8)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (8)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (5)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (7)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (8)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5904
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-19)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-34)) (.leaf (-38)))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (-9)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 32 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.branch 26 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 37 (.leaf (-36)) (.branch 48 (.leaf (-35)) (.leaf (-30))))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 42 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.branch 17 (.branch 6 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.leaf (-26)))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 33 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_309_5905 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (7)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (8)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5905
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 52 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 22 (.leaf (0)) (.leaf (-32))),
  (.branch 49 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 53 (.leaf (-8)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.leaf (-29)))) (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.leaf (-21)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.leaf (-17)))))) (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5906 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (8)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 26 (.leaf (6)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (7)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (8))) (.branch 53 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5906
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.branch 37 (.leaf (14)) (.leaf (15))))) (.branch 47 (.branch 42 (.leaf (16)) (.branch 45 (.leaf (17)) (.leaf (18)))) (.branch 50 (.leaf (19)) (.branch 53 (.leaf (20)) (.leaf (21))))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 51 (.branch 40 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))) (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_309_5907 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (1))) (.branch 26 (.leaf (3)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (7))) (.branch 39 (.leaf (1)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (1))) (.branch 53 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5907
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 33 (.leaf (-8)) (.branch 49 (.leaf (-9)) (.leaf (-11))))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.branch 50 (.branch 48 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_309_5908 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (8))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (6)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (7))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (1))) (.branch 53 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5908
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 50 (.branch 36 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 48 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_309_5909 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (4)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (5)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (4)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (8)) (.branch 42 (.leaf (6)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5909
  counts := ![(.branch 24 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 28 (.leaf (-16)) (.branch 33 (.leaf (-18)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 34 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18)))) (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-14)) (.leaf (-11))))),
  (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 48 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessP9_309_5910 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (3)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (1)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_5910
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 17 (.leaf (0)) (.leaf (-37))),
  (.branch 44 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 50 (.branch 36 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20))))))) (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5911 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (3)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (6)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (8))) (.branch 46 (.leaf (4)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5911
  counts := ![(.branch 23 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-22)) (.leaf (-24)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 41 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 30 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-22))),
  (.branch 18 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 51 (.branch 34 (.leaf (-24)) (.branch 45 (.leaf (-23)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.leaf (-6)) (.leaf (-4))),
  (.branch 51 (.branch 43 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-16)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (-29)) (.leaf (-28))) (.branch 20 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 52 (.leaf (-23)) (.branch 53 (.leaf (-17)) (.leaf (-11)))))),
  (.branch 39 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (0)))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 43 (.branch 37 (.branch 34 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-20)) (.branch 36 (.leaf (-19)) (.leaf (-18))))) (.branch 40 (.branch 38 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5912 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (5)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (4)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (3))) (.branch 53 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5912
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 11 (.leaf (-24)) (.leaf (-26)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-39)) (.leaf (-42)))),
  (.branch 8 (.leaf (0)) (.branch 51 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 51 (.branch 39 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.leaf (-8)) (.leaf (-5))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 46 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 49 (.branch 36 (.branch 25 (.leaf (-42)) (.leaf (-41))) (.branch 47 (.leaf (-40)) (.branch 48 (.leaf (-35)) (.leaf (-30))))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5913 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (7)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (8)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (4))) (.branch 53 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5913
  counts := ![(.branch 22 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 28 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 49 (.leaf (-27)) (.leaf (-34)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 48 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 37 (.leaf (-18)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.branch 50 (.leaf (-34)) (.leaf (-30))) (.branch 52 (.leaf (-26)) (.branch 53 (.leaf (-22)) (.leaf (-18))))),
  (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 51 (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 48 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 49 (.leaf (-18)) (.leaf (-16)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_309_5914 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (6)) (.leaf (8)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (7)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (8)) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (0)) (.leaf (7)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5914
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 37 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5915 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (8)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (3)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (8)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (7))) (.branch 26 (.leaf (2)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (7)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (6))) (.branch 39 (.leaf (3)) (.leaf (8)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (7)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (8))) (.branch 53 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5915
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-26)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 26 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 43 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-24)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 50 (.branch 42 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 49 (.leaf (-24)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 45 (.branch 31 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-1)),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 28 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 41 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))]
def witnessP9_309_5916 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (8)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (2)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (8)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (5)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (8)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (7)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5916
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 22 (.leaf (-24)) (.leaf (-25)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 30 (.leaf (-10)) (.branch 52 (.leaf (-12)) (.leaf (-14))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-19)) (.leaf (-23)))),
  (.branch 31 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-12)) (.leaf (-15)))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.leaf (-14)) (.leaf (-11))),
  (.branch 36 (.branch 20 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 53 (.leaf (-13)) (.leaf (-8))))),
  (.branch 39 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (0)))),
  (.branch 50 (.branch 48 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-2)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5917 : CycleWitness 9 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (8)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (1)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (5)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (2)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (6)) (.leaf (4))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (1)))) (.branch 51 (.branch 50 (.leaf (8)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5917
  counts := ![(.branch 27 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-5)))) (.branch 36 (.branch 29 (.leaf (-6)) (.leaf (-7))) (.branch 47 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-35)) (.leaf (-42)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 48 (.leaf (-22)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 46 (.leaf (-20)) (.leaf (-26)))),
  (.branch 39 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 30 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-35)) (.leaf (-37)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 52 (.leaf (-9)) (.leaf (-8))),
  (.branch 38 (.branch 20 (.branch 14 (.leaf (-42)) (.leaf (-41))) (.branch 26 (.leaf (-40)) (.branch 32 (.leaf (-39)) (.leaf (-38))))) (.branch 50 (.branch 44 (.leaf (-37)) (.leaf (-36))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 50 (.branch 49 (.leaf (-25)) (.leaf (-21))) (.branch 51 (.leaf (-17)) (.branch 52 (.leaf (-13)) (.leaf (-9))))),
  (.branch 25 (.leaf (-6)) (.branch 39 (.leaf (-5)) (.leaf (-4)))),
  (.branch 49 (.branch 47 (.leaf (-26)) (.branch 48 (.leaf (-23)) (.leaf (-20)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-14))) (.branch 52 (.leaf (-11)) (.leaf (-8))))),
  (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-3)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-37)) (.branch 42 (.leaf (-36)) (.leaf (-33)))) (.branch 44 (.leaf (-30)) (.branch 45 (.leaf (-27)) (.leaf (-24))))) (.branch 49 (.branch 47 (.leaf (-21)) (.branch 48 (.leaf (-18)) (.leaf (-15)))) (.branch 51 (.branch 50 (.leaf (-12)) (.leaf (-9))) (.branch 52 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 52 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_309_5918 : CycleWitness 9 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (6)) (.leaf (0)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (1)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (2)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (8)) (.leaf (2))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (1)))) (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5918
  counts := ![(.branch 27 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-5)))) (.branch 36 (.branch 29 (.leaf (-6)) (.leaf (-7))) (.branch 47 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-35)) (.leaf (-42)))),
  (.branch 39 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 48 (.leaf (-22)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-35)) (.leaf (-37)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-45)) (.leaf (-46)))),
  (.branch 17 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.leaf (-9)) (.leaf (-8))),
  (.branch 38 (.branch 20 (.branch 14 (.leaf (-42)) (.leaf (-41))) (.branch 26 (.leaf (-40)) (.branch 32 (.leaf (-39)) (.leaf (-38))))) (.branch 50 (.branch 44 (.leaf (-37)) (.leaf (-36))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 47 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-7)) (.leaf (0)))),
  (.branch 50 (.branch 49 (.leaf (-25)) (.leaf (-21))) (.branch 51 (.leaf (-17)) (.branch 52 (.leaf (-13)) (.leaf (-9))))),
  (.branch 25 (.leaf (-6)) (.branch 39 (.leaf (-5)) (.leaf (-4)))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-37)) (.branch 42 (.leaf (-36)) (.leaf (-33)))) (.branch 44 (.leaf (-30)) (.branch 45 (.leaf (-27)) (.leaf (-24))))) (.branch 49 (.branch 47 (.leaf (-21)) (.branch 48 (.leaf (-18)) (.leaf (-15)))) (.branch 51 (.branch 50 (.leaf (-12)) (.leaf (-9))) (.branch 52 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 52 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-46)) (.leaf (-44))) (.branch 33 (.leaf (-42)) (.branch 34 (.leaf (-40)) (.leaf (-38))))) (.branch 38 (.branch 36 (.leaf (-36)) (.branch 37 (.leaf (-34)) (.leaf (-32)))) (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-28)) (.leaf (-26)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (-24)) (.branch 43 (.leaf (-22)) (.leaf (-20)))) (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-16)) (.leaf (-14))))) (.branch 50 (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-10)) (.leaf (-8)))) (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 48 (.branch 46 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_309_5919 : CycleWitness 9 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (7)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (5)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (8)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (2)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (4)) (.branch 48 (.leaf (0)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (5))) (.branch 52 (.leaf (1)) (.leaf (7))))))))
  code := certificateP9_5919
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 42 (.leaf (-44)) (.leaf (-46)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-35)) (.leaf (-37)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-4)) (.branch 51 (.leaf (-9)) (.leaf (-12))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.leaf (-15))) (.branch 45 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 50 (.branch 43 (.leaf (-46)) (.branch 49 (.leaf (-45)) (.leaf (-36)))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-2)),
  (.branch 37 (.branch 23 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24)))) (.branch 51 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 52 (.leaf (-17)) (.leaf (-12))))),
  (.branch 50 (.branch 34 (.leaf (-16)) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 51 (.leaf (-11)) (.branch 52 (.leaf (-8)) (.leaf (-5))))),
  (.branch 49 (.branch 39 (.leaf (-37)) (.branch 48 (.leaf (-36)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-24)) (.leaf (-18))) (.branch 52 (.leaf (-12)) (.leaf (-6))))),
  (.branch 52 (.leaf (-12)) (.leaf (-10))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_309_5920 : CycleWitness 9 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (1)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (7)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (8))) (.branch 25 (.leaf (0)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (2)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (6)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (8)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (5))) (.branch 45 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 47 (.leaf (1)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (7)) (.leaf (6))) (.branch 52 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5920
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-44))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 27 (.leaf (-32)) (.leaf (-35)))),
  (.branch 22 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 36 (.leaf (-18)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.branch 44 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.leaf (0)) (.branch 51 (.leaf (-3)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.branch 50 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.leaf (-35)))]
  high := ![(.branch 32 (.branch 14 (.branch 2 (.leaf (-44)) (.branch 8 (.leaf (-43)) (.leaf (-42)))) (.branch 20 (.leaf (-41)) (.branch 26 (.leaf (-40)) (.leaf (-39))))) (.branch 50 (.branch 38 (.leaf (-38)) (.branch 44 (.leaf (-37)) (.leaf (-36)))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9)))))),
  (.leaf (-2)),
  (.branch 49 (.branch 35 (.branch 28 (.leaf (-35)) (.leaf (-34))) (.branch 42 (.leaf (-33)) (.leaf (-32)))) (.branch 51 (.branch 50 (.leaf (-27)) (.leaf (-22))) (.branch 52 (.leaf (-17)) (.leaf (-12))))),
  (.branch 46 (.leaf (-3)) (.leaf (0))),
  (.branch 49 (.branch 47 (.branch 37 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-20)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.leaf (-10))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.leaf (-14)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-10))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 52 (.leaf (-6)) (.leaf (-4))),
  (.branch 51 (.leaf (-9)) (.branch 52 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 43 (.branch 7 (.leaf (-35)) (.branch 25 (.leaf (-34)) (.leaf (-33)))) (.branch 44 (.leaf (-30)) (.branch 45 (.leaf (-27)) (.leaf (-24))))) (.branch 49 (.branch 47 (.leaf (-21)) (.branch 48 (.leaf (-18)) (.leaf (-15)))) (.branch 51 (.branch 50 (.leaf (-12)) (.leaf (-9))) (.branch 52 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_309_5921 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (8)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (6))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5921
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 46 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-39))),
  (.branch 39 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.leaf (-4)) (.leaf (-2))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5922 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (6))))))) (.branch 39 (.branch 33 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 46 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 49 (.branch 47 (.leaf (8)) (.leaf (0))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5922
  counts := ![(.branch 25 (.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 23 (.leaf (14)) (.leaf (15)))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (16)) (.leaf (17))) (.branch 30 (.leaf (18)) (.leaf (19)))) (.branch 35 (.branch 33 (.leaf (20)) (.leaf (21))) (.branch 36 (.leaf (22)) (.leaf (23))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (24)) (.leaf (25))) (.branch 43 (.leaf (26)) (.leaf (27)))) (.branch 48 (.branch 46 (.leaf (28)) (.leaf (29))) (.branch 49 (.leaf (30)) (.branch 51 (.leaf (31)) (.leaf (32)))))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.leaf (-11)) (.leaf (-8))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5923 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (7))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (5)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (6)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5923
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_309_5924 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (8)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (0))))) (.branch 49 (.branch 47 (.leaf (7)) (.leaf (0))) (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5924
  counts := ![(.branch 25 (.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 23 (.leaf (14)) (.leaf (15)))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (16)) (.leaf (17))) (.branch 30 (.leaf (18)) (.leaf (19)))) (.branch 35 (.branch 33 (.leaf (20)) (.leaf (21))) (.branch 36 (.leaf (22)) (.leaf (23))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (24)) (.leaf (25))) (.branch 43 (.leaf (26)) (.leaf (27)))) (.branch 48 (.branch 46 (.leaf (28)) (.leaf (29))) (.branch 49 (.leaf (30)) (.branch 51 (.leaf (31)) (.leaf (32)))))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-44))),
  (.branch 34 (.leaf (0)) (.leaf (-18))),
  (.branch 47 (.leaf (0)) (.leaf (-5))),
  (.branch 21 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 50 (.leaf (-11)) (.leaf (-8))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-44)) (.leaf (-43))) (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40))))) (.branch 16 (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_309_5925 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (8)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (7)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5925
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21))),
  (.branch 44 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-34)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_309_5926 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (8))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 44 (.leaf (6)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5926
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 25 (.leaf (-32)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_309_5927 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (8)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (7)) (.branch 45 (.leaf (1)) (.leaf (0))))) (.branch 49 (.branch 47 (.leaf (2)) (.branch 48 (.leaf (0)) (.leaf (1)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5927
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 40 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.branch 15 (.leaf (-11)) (.leaf (-12))))) (.branch 30 (.branch 28 (.leaf (-13)) (.leaf (-14))) (.branch 41 (.leaf (-15)) (.branch 43 (.leaf (-16)) (.leaf (-17)))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21))),
  (.branch 44 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-34)))]
  high := ![(.branch 44 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-12)))),
  (.branch 46 (.leaf (-2)) (.leaf (0))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_309_5928 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (7)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (0)))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (0)))) (.branch 44 (.leaf (6)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5928
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 46 (.branch 43 (.branch 25 (.leaf (-32)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_309_5929 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (6)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (7)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (6)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (8)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5929
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-27)) (.leaf (-30)))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-29))),
  (.branch 49 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.branch 49 (.leaf (-3)) (.leaf (0))),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-30)) (.branch 39 (.leaf (-29)) (.leaf (-27)))) (.branch 42 (.branch 41 (.leaf (-25)) (.leaf (-23))) (.branch 43 (.leaf (-21)) (.leaf (-19))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-17)) (.leaf (-15))) (.branch 47 (.leaf (-13)) (.leaf (-11)))) (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 34 (.leaf (-4)) (.leaf (-3))),
  (.branch 46 (.branch 26 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_309_5930 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5930
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 36 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 39 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 25 (.leaf (0)) (.leaf (-27))),
  (.branch 51 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 45 (.branch 41 (.leaf (-6)) (.leaf (-4))) (.branch 49 (.leaf (-2)) (.leaf (0)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_309_5931 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (0))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (2)) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (5))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5931
  counts := ![(.branch 24 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 34 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-18))) (.branch 42 (.leaf (-19)) (.branch 48 (.leaf (-21)) (.leaf (-24))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 27 (.leaf (-17)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 47 (.leaf (-24)) (.leaf (-29)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 25 (.leaf (0)) (.leaf (-27))),
  (.leaf (0))]
  high := ![(.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-24)) (.leaf (-19))) (.branch 51 (.leaf (-14)) (.leaf (-9)))),
  (.branch 36 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.leaf (-18)))),
  (.branch 49 (.branch 48 (.leaf (-29)) (.leaf (-24))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 40 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-5)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 40 (.branch 12 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_309_5932 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5932
  counts := ![(.branch 25 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (11)) (.branch 28 (.leaf (12)) (.leaf (13)))) (.branch 33 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))) (.branch 46 (.branch 41 (.leaf (17)) (.branch 43 (.leaf (18)) (.leaf (19)))) (.branch 48 (.leaf (20)) (.branch 51 (.leaf (21)) (.leaf (22))))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 28 (.leaf (-26)) (.leaf (-34)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 44 (.leaf (-3)) (.leaf (-5)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 45 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.branch 29 (.leaf (-34)) (.branch 34 (.leaf (-33)) (.leaf (-32)))) (.branch 44 (.leaf (-31)) (.branch 49 (.leaf (-30)) (.leaf (-25))))),
  (.branch 43 (.branch 36 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 45 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 48 (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_309_5933 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (8))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5933
  counts := ![(.branch 25 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (11)) (.branch 28 (.leaf (12)) (.leaf (13)))) (.branch 33 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))) (.branch 46 (.branch 41 (.leaf (17)) (.branch 43 (.leaf (18)) (.leaf (19)))) (.branch 48 (.leaf (20)) (.branch 51 (.leaf (21)) (.leaf (22))))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 28 (.leaf (-26)) (.leaf (-34)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 45 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.branch 29 (.leaf (-34)) (.branch 34 (.leaf (-33)) (.leaf (-32)))) (.branch 44 (.leaf (-31)) (.branch 49 (.leaf (-30)) (.leaf (-25))))),
  (.branch 43 (.branch 36 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_309_5934 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (8)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5934
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 36 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 39 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-8)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-34)) (.leaf (-35)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-7))) (.branch 49 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 17 (.leaf (0)) (.leaf (-35))),
  (.branch 43 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 48 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 45 (.branch 41 (.leaf (-6)) (.leaf (-4))) (.branch 49 (.leaf (-2)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 49 (.branch 47 (.leaf (-10)) (.branch 48 (.leaf (-9)) (.leaf (-8)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-35)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.leaf (-32)))) (.branch 23 (.branch 22 (.leaf (-31)) (.leaf (-30))) (.branch 24 (.leaf (-29)) (.leaf (-28))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))))) (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_309_5935 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (7))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (8))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5935
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 46 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-4)) (.leaf (-2))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5936 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (8))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (5))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (6))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5936
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-7)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 42 (.leaf (-10)) (.leaf (-12)))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 33 (.leaf (0)) (.leaf (-19))),
  (.branch 7 (.leaf (0)) (.leaf (-45)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-4)) (.leaf (-2))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 49 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 17 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-45)) (.leaf (-44))) (.branch 10 (.leaf (-43)) (.branch 11 (.leaf (-42)) (.leaf (-41))))) (.branch 15 (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38)))) (.branch 16 (.leaf (-37)) (.branch 17 (.leaf (-36)) (.leaf (-35)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.branch 22 (.leaf (-31)) (.leaf (-30))))) (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_309_5937 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (7))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (6)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (5)) (.leaf (0)))) (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5937
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_309_5938 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5938
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 49 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 51 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-8)))) (.branch 30 (.leaf (-9)) (.branch 43 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-43))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 35 (.leaf (0)) (.leaf (-17))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 47 (.leaf (-10)) (.leaf (-6))),
  (.branch 44 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 30 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-43)) (.leaf (-42))) (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39))))) (.branch 16 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_309_5939 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5939
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 49 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 51 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-8)))) (.branch 30 (.leaf (-9)) (.branch 43 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 47 (.leaf (-10)) (.leaf (-6))),
  (.branch 44 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_309_5940 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5940
  counts := ![(.branch 23 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 20 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))) (.branch 40 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-42))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 36 (.leaf (0)) (.leaf (-16))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-10)))),
  (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-2)) (.leaf (0))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 31 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-42)) (.leaf (-41))) (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38))))) (.branch 17 (.branch 16 (.leaf (-37)) (.leaf (-36))) (.branch 18 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_309_5941 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5941
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))) (.branch 30 (.leaf (-8)) (.branch 43 (.leaf (-10)) (.leaf (-12))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 39 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-15)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 18 (.leaf (0)) (.leaf (-34))),
  (.branch 36 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 43 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 44 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))),
  (.branch 50 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.branch 45 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 46 (.leaf (-15)) (.leaf (-13)))) (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_309_5942 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5942
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 9 (.branch 7 (.leaf (-9)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.leaf (-12))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-40))) (.branch 38 (.leaf (-41)) (.leaf (-42)))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-28)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 39 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-39)))]
  high := ![(.branch 51 (.leaf (-12)) (.leaf (-6))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-42)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 13 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 47 (.branch 44 (.branch 26 (.leaf (-29)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_309_5943 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (7)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5943
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 9 (.branch 7 (.leaf (-9)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-40))),
  (.branch 25 (.leaf (0)) (.leaf (-27))),
  (.branch 38 (.leaf (0)) (.leaf (-14))),
  (.branch 51 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.leaf (-12)) (.leaf (-6))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 32 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-40)) (.leaf (-39))) (.branch 15 (.leaf (-38)) (.branch 16 (.leaf (-37)) (.leaf (-36))))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_309 : Fin 56 → CycleWitness 9 := ![witnessP9_309_5888, witnessP9_309_5889, witnessP9_309_5890, witnessP9_309_5891, witnessP9_309_5892, witnessP9_309_5893, witnessP9_309_5894, witnessP9_309_5895, witnessP9_309_5896, witnessP9_309_5897, witnessP9_309_5898, witnessP9_309_5899, witnessP9_309_5900, witnessP9_309_5901, witnessP9_309_5902, witnessP9_309_5903, witnessP9_309_5904, witnessP9_309_5905, witnessP9_309_5906, witnessP9_309_5907, witnessP9_309_5908, witnessP9_309_5909, witnessP9_309_5910, witnessP9_309_5911, witnessP9_309_5912, witnessP9_309_5913, witnessP9_309_5914, witnessP9_309_5915, witnessP9_309_5916, witnessP9_309_5917, witnessP9_309_5918, witnessP9_309_5919, witnessP9_309_5920, witnessP9_309_5921, witnessP9_309_5922, witnessP9_309_5923, witnessP9_309_5924, witnessP9_309_5925, witnessP9_309_5926, witnessP9_309_5927, witnessP9_309_5928, witnessP9_309_5929, witnessP9_309_5930, witnessP9_309_5931, witnessP9_309_5932, witnessP9_309_5933, witnessP9_309_5934, witnessP9_309_5935, witnessP9_309_5936, witnessP9_309_5937, witnessP9_309_5938, witnessP9_309_5939, witnessP9_309_5940, witnessP9_309_5941, witnessP9_309_5942, witnessP9_309_5943]
end RealPinwheel.FiveSixths


