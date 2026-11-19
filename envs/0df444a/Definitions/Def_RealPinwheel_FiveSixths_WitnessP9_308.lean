-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_308
-- name    : RealPinwheel_FiveSixths_WitnessP9_308
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:22.559087+00:00
-- url     : https://prove2.me/theorems/aa769338-be4d-4446-8759-e1da08e6b29b
-- title:
--   Exact witness block P9_308
-- statement:
--   These exact witnesses represent words 5834 through 5888 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5834–5888; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_308_5833 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (2)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (6))) (.branch 53 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5833
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.leaf (-3)) (.leaf (-2))),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5834 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5834
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-9)) (.branch 45 (.leaf (-14)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 21 (.leaf (0)) (.leaf (-33))),
  (.branch 48 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.leaf (-30)))) (.branch 27 (.branch 26 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.leaf (-26))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.leaf (-18)))))) (.branch 45 (.branch 41 (.branch 39 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 40 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5835 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5835
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-9)) (.branch 45 (.leaf (-14)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.leaf (0)) (.branch 44 (.leaf (-4)) (.leaf (-7)))),
  (.branch 21 (.leaf (0)) (.leaf (-33))),
  (.branch 48 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-47))),
  (.branch 34 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 45 (.leaf (-7)) (.leaf (-5))) (.branch 47 (.leaf (-3)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.leaf (-30)))) (.branch 27 (.branch 26 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.leaf (-26))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.leaf (-18)))))) (.branch 45 (.branch 41 (.branch 39 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 40 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-47)) (.leaf (-46))) (.branch 10 (.leaf (-45)) (.branch 11 (.leaf (-44)) (.leaf (-43))))) (.branch 15 (.branch 13 (.leaf (-42)) (.branch 14 (.leaf (-41)) (.leaf (-40)))) (.branch 16 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-36)) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31))))) (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5836 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5836
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-9)) (.branch 45 (.leaf (-14)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5837 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (7))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (6)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (7))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (3)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5837
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-7)) (.leaf (-9)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-13)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 49 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-6)))),
  (.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 31 (.leaf (-16)) (.branch 41 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 51 (.branch 38 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 32 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5838 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (7)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (6)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5838
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 38 (.leaf (-14)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 19 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-3)),
  (.branch 39 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-11)))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 13 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5839 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5839
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-13)) (.leaf (-16)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 49 (.leaf (-13)) (.leaf (-11)))),
  (.branch 46 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))),
  (.branch 52 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 48 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_308_5840 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (8)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (8))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (7)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (6)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5840
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-19)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 46 (.leaf (-11)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 38 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5841 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (8)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (7)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (5)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (8)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (6)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (7)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (8)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_5841
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-14))) (.branch 39 (.leaf (-16)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.branch 49 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 42 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.leaf (-12))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))]
def witnessP9_308_5842 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (6))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5842
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-17)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 20 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-47))),
  (.branch 34 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-13))))),
  (.branch 45 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 52 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-47)) (.leaf (-46))) (.branch 10 (.leaf (-45)) (.branch 11 (.leaf (-44)) (.leaf (-43))))) (.branch 15 (.branch 13 (.leaf (-42)) (.branch 14 (.leaf (-41)) (.leaf (-40)))) (.branch 16 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-36)) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31))))) (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5843 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (6))) (.branch 39 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (5)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5843
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-20)) (.leaf (-24)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 48 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-8)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 25 (.leaf (0)) (.leaf (-29))),
  (.branch 52 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.branch 40 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.leaf (-4)) (.leaf (-3))),
  (.branch 45 (.branch 31 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-3)) (.leaf (0))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 5 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 30 (.branch 29 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.leaf (-23))))) (.branch 35 (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_308_5844 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (8))) (.branch 26 (.leaf (6)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (7))) (.branch 39 (.leaf (0)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (5)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5844
  counts := ![(.branch 24 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-20)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 25 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 44 (.branch 36 (.leaf (-25)) (.branch 40 (.leaf (-24)) (.leaf (-23)))) (.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-16)) (.leaf (-14)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_308_5845 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (7)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (5)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5845
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-33)) (.leaf (-36)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 45 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.branch 19 (.leaf (-36)) (.branch 50 (.leaf (-35)) (.leaf (-28)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 46 (.leaf (-9)) (.leaf (-7))),
  (.branch 42 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5846 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (6)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (8)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (5)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (7)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (6)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5846
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-12))) (.branch 41 (.leaf (-14)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 51 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 41 (.branch 33 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 39 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.leaf (-3)) (.leaf (-2))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4))))]
def witnessP9_308_5847 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (1)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (4)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (5)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (1)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5847
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 11 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 47 (.leaf (-34)) (.leaf (-35)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 51 (.branch 39 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 48 (.leaf (-35)) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_308_5848 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (8)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (6)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5848
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.leaf (-7)))) (.branch 51 (.branch 50 (.leaf (-6)) (.leaf (-5))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessP9_308_5849 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (8))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (8))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5849
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-17)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 20 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-13))))),
  (.branch 45 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 52 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5850 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (8)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5850
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 38 (.leaf (-14)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 31 (.leaf (0)) (.leaf (-23))),
  (.branch 49 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-3)),
  (.branch 39 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-11)))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5851 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5851
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-39))),
  (.branch 33 (.leaf (0)) (.leaf (-21))),
  (.branch 51 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-39)) (.leaf (-38))) (.branch 18 (.leaf (-37)) (.leaf (-36)))) (.branch 21 (.branch 20 (.leaf (-35)) (.leaf (-34))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-30)) (.leaf (-29))) (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.branch 33 (.leaf (-22)) (.leaf (-21))))))) (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5852 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (7)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (8))) (.branch 26 (.leaf (5)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (2)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (8)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (7))) (.branch 53 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5852
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-24)) (.leaf (-27)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 28 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 50 (.branch 48 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5853 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (8))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 26 (.leaf (1)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (8))) (.branch 39 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (6)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (7))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5853
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-20)) (.leaf (-24)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 48 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 48 (.branch 40 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.leaf (-4)) (.leaf (-3))),
  (.branch 51 (.branch 31 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 5 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5854 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (7))) (.branch 46 (.leaf (1)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (6)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5854
  counts := ![(.branch 23 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-22)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-8)))) (.branch 38 (.leaf (-13)) (.branch 43 (.leaf (-14)) (.leaf (-19))))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 51 (.branch 34 (.leaf (-24)) (.branch 45 (.leaf (-23)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 47 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-4)))),
  (.branch 31 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))),
  (.branch 52 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 53 (.leaf (-16)) (.leaf (-14)))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5855 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (8)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (5)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (8)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5855
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5856 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (7))) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5856
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))) (.branch 47 (.branch 42 (.leaf (10)) (.leaf (11))) (.branch 50 (.leaf (12)) (.leaf (13)))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))) (.branch 49 (.branch 45 (.leaf (10)) (.leaf (11))) (.branch 53 (.leaf (12)) (.leaf (13)))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))) (.branch 17 (.branch 13 (.leaf (-21)) (.leaf (-22))) (.branch 50 (.leaf (-23)) (.leaf (-25))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))) (.branch 40 (.branch 36 (.leaf (-8)) (.leaf (-9))) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-6)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-16)) (.leaf (-19)))),
  (.branch 24 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (-16)) (.leaf (-17)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 52 (.branch 51 (.leaf (-25)) (.leaf (-19))) (.branch 53 (.leaf (-13)) (.leaf (-7)))),
  (.leaf (-11)),
  (.branch 47 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-4)))),
  (.branch 22 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.branch 49 (.leaf (-19)) (.branch 50 (.leaf (-17)) (.leaf (-15)))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-11)) (.leaf (-9))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 41 (.branch 39 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 40 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5857 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (8)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (8))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (7)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (6))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5857
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 21 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 48 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-13)) (.branch 38 (.leaf (-18)) (.leaf (-22))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 37 (.leaf (-18)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 49 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-6)))),
  (.branch 51 (.branch 39 (.leaf (-22)) (.branch 45 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-14)) (.leaf (-11))))),
  (.branch 50 (.branch 48 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 49 (.leaf (-18)) (.leaf (-16)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5858 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (8))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (3)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (7))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_5858
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 50 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-15))) (.branch 38 (.leaf (-17)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.branch 48 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-8))) (.branch 53 (.leaf (-6)) (.leaf (-4)))),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.leaf (-12))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 51 (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))]
def witnessP9_308_5859 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (8)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (5)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5859
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-33)) (.leaf (-36)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 45 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-16))))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.branch 19 (.leaf (-36)) (.branch 50 (.leaf (-35)) (.leaf (-28)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 46 (.leaf (-9)) (.leaf (-7))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4))))))]
def witnessP9_308_5860 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (7)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (1)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5860
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-34))) (.branch 7 (.leaf (-42)) (.leaf (-50)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 34 (.leaf (-24)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 50 (.leaf (-3)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 25 (.leaf (0)) (.leaf (-29))),
  (.branch 39 (.leaf (0)) (.leaf (-15))),
  (.branch 52 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.branch 8 (.leaf (-50)) (.branch 37 (.leaf (-49)) (.leaf (-47)))) (.branch 52 (.leaf (-42)) (.branch 53 (.leaf (-29)) (.leaf (-16))))),
  (.branch 46 (.branch 35 (.leaf (-28)) (.leaf (-26))) (.branch 50 (.leaf (-21)) (.leaf (-16)))),
  (.branch 38 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (0)))),
  (.branch 49 (.branch 47 (.branch 24 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.leaf (-7)))) (.branch 51 (.branch 50 (.leaf (-6)) (.leaf (-5))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 52 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 53 (.leaf (-3)) (.leaf (-2)))),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 32 (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 30 (.branch 29 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.leaf (-23))))) (.branch 35 (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_308_5861 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (7)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5861
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 18 (.leaf (0)) (.leaf (-36))),
  (.branch 36 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 48 (.leaf (-17)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))))) (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_308_5862 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (7)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (0))) (.branch 26 (.leaf (1)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (7)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5862
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5863 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (4)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (8)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (7)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5863
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 6 (.leaf (-6)) (.branch 33 (.leaf (-9)) (.leaf (-11))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-16)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 49 (.leaf (-13)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-15))),
  (.branch 26 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 53 (.leaf (-8)) (.leaf (-6)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_308_5864 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (6)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5864
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 41 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 49 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-20)) (.branch 44 (.leaf (-25)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-17)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 23 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-45))),
  (.branch 36 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 52 (.branch 45 (.leaf (-28)) (.leaf (-27))) (.branch 53 (.leaf (-20)) (.leaf (-13)))),
  (.branch 38 (.branch 30 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))) (.branch 46 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 48 (.leaf (-20)) (.branch 49 (.leaf (-18)) (.leaf (-16)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 49 (.branch 47 (.branch 33 (.leaf (-17)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-45)) (.leaf (-44))) (.branch 12 (.leaf (-43)) (.branch 13 (.leaf (-42)) (.leaf (-41))))) (.branch 17 (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38)))) (.branch 18 (.leaf (-37)) (.branch 19 (.leaf (-36)) (.leaf (-35)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-34)) (.leaf (-33))) (.branch 23 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30))))) (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 29 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-24))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5865 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (8))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (7))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (7))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (8))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (7))))))))
  code := certificateP9_5865
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 42 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 50 (.branch 48 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))]
def witnessP9_308_5866 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (8)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (5)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (8))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (7)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (6)) (.leaf (8)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5866
  counts := ![(.branch 24 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-20)) (.leaf (-26)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.leaf (0)) (.branch 49 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-12)) (.leaf (-13)))),
  (.branch 15 (.leaf (0)) (.branch 50 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 44 (.branch 36 (.branch 32 (.leaf (-26)) (.leaf (-25))) (.branch 40 (.leaf (-24)) (.leaf (-23)))) (.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 39 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 47 (.branch 43 (.branch 23 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 44 (.branch 24 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5867 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (8)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (8)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (7))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5867
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 42 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 27 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 37 (.branch 34 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-20)) (.branch 36 (.leaf (-19)) (.leaf (-18))))) (.branch 40 (.branch 38 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5868 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (7))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5868
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5869 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (8)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (8)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_5869
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 12 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-14)))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (-24))) (.branch 33 (.leaf (-26)) (.leaf (-30)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 21 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 50 (.branch 34 (.leaf (-30)) (.branch 42 (.leaf (-29)) (.leaf (-28)))) (.branch 52 (.branch 51 (.leaf (-23)) (.leaf (-18))) (.branch 53 (.leaf (-13)) (.leaf (-8))))),
  (.branch 7 (.leaf (-9)) (.leaf (-8))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5870 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (8))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5870
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-5)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-48))),
  (.branch 18 (.leaf (0)) (.leaf (-36))),
  (.branch 33 (.leaf (0)) (.leaf (-21))),
  (.branch 45 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.leaf (-9)) (.branch 48 (.leaf (-8)) (.leaf (-5)))),
  (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.branch 41 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 30 (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-48)) (.branch 8 (.leaf (-47)) (.leaf (-46)))) (.branch 10 (.leaf (-45)) (.branch 11 (.leaf (-44)) (.leaf (-43))))) (.branch 15 (.branch 13 (.leaf (-42)) (.branch 14 (.leaf (-41)) (.leaf (-40)))) (.branch 16 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-36)) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31))))) (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))))) (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5871 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (6)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (8)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (7)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (5)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (8)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5871
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-19)) (.leaf (-20)))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 31 (.leaf (-7)) (.branch 53 (.leaf (-9)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-11)),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5872 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (8))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (2)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (8))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (6))) (.branch 53 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5872
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 48 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 37 (.leaf (-9)) (.branch 48 (.leaf (-8)) (.leaf (-5)))),
  (.branch 51 (.branch 31 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5873 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (7)) (.branch 42 (.leaf (2)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (6)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5873
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-1)) (.leaf (-2)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 46 (.leaf (-11)) (.leaf (-14)))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 38 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5874 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (2))) (.branch 26 (.leaf (4)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (7))) (.branch 39 (.leaf (1)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (6))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (2))) (.branch 53 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5874
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 48 (.leaf (-6)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 31 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8)))) (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5875 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (8))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (8))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (6)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5875
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (-3))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 20 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-13))))),
  (.branch 45 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 52 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5876 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (1)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (2)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (5))) (.branch 39 (.leaf (2)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (1)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5876
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-6)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 38 (.leaf (-16)) (.leaf (-19)))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.branch 50 (.branch 36 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 40 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 39 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-16)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_308_5877 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (8))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (8)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (7))))))))
  code := certificateP9_5877
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 41 (.branch 33 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 12 (.leaf (-19)) (.leaf (-21)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-6)))) (.branch 42 (.leaf (-8)) (.branch 47 (.leaf (-10)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 51 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.leaf (-12)) (.leaf (-11))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 49 (.branch 47 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5878 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (7))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (6)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (8))) (.branch 39 (.leaf (4)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (6))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (7)) (.leaf (4))))))))
  code := certificateP9_5878
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 46 (.leaf (9)) (.branch 52 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-43)) (.leaf (-46)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))) (.branch 42 (.branch 37 (.leaf (-11)) (.leaf (-14))) (.branch 46 (.leaf (-15)) (.leaf (-18))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-29)) (.leaf (-33)))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 25 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.branch 38 (.leaf (-15)) (.leaf (-20))))]
  high := ![(.branch 51 (.branch 41 (.leaf (-46)) (.branch 46 (.leaf (-45)) (.leaf (-44)))) (.branch 52 (.leaf (-33)) (.branch 53 (.leaf (-22)) (.leaf (-11))))),
  (.branch 47 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-15)))),
  (.branch 44 (.branch 28 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-9)) (.leaf (-5))))),
  (.branch 51 (.branch 25 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-33)) (.leaf (-32))) (.branch 46 (.leaf (-29)) (.branch 47 (.leaf (-26)) (.leaf (-23))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-17)) (.leaf (-14)))) (.branch 52 (.leaf (-11)) (.branch 53 (.leaf (-8)) (.leaf (-5)))))),
  (.branch 50 (.branch 48 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-19))) (.branch 41 (.leaf (-18)) (.leaf (-17)))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5))))))]
def witnessP9_308_5879 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (8))) (.branch 26 (.leaf (1)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (7)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5879
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 22 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.leaf (-15))),
  (.branch 25 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 47 (.branch 35 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 46 (.branch 42 (.branch 22 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_308_5880 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (8))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (5)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (7))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (1)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5880
  counts := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-7)) (.branch 52 (.leaf (-10)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (-39)) (.leaf (-41)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-23)))),
  (.branch 10 (.leaf (0)) (.branch 53 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-13)) (.leaf (-11))),
  (.branch 49 (.branch 47 (.branch 36 (.leaf (-41)) (.leaf (-40))) (.branch 48 (.leaf (-35)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 40 (.branch 18 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-21)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_308_5881 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (8))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (5))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (5))) (.branch 39 (.leaf (4)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (6))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5881
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 46 (.leaf (9)) (.branch 52 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-43)) (.leaf (-46)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))) (.branch 42 (.branch 37 (.leaf (-11)) (.leaf (-14))) (.branch 46 (.leaf (-15)) (.leaf (-18))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (-1))) (.branch 38 (.leaf (-8)) (.leaf (-11)))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-23)) (.leaf (-24)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 51 (.branch 41 (.leaf (-46)) (.branch 46 (.leaf (-45)) (.leaf (-44)))) (.branch 52 (.leaf (-33)) (.branch 53 (.leaf (-22)) (.leaf (-11))))),
  (.branch 47 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-15)))),
  (.branch 44 (.branch 28 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-9)) (.leaf (-5))))),
  (.branch 51 (.branch 25 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.leaf (-11)) (.leaf (-10))),
  (.branch 50 (.branch 48 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5882 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (8)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (3))) (.branch 26 (.leaf (7)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (5)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (0))) (.branch 46 (.leaf (3)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (7)) (.leaf (5))))))))
  code := certificateP9_5882
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 46 (.leaf (-39)) (.leaf (-40)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 49 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-40)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.branch 29 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.branch 36 (.leaf (-11)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_308_5883 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (3)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (5)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (2)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5883
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 52 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-33))) (.branch 41 (.leaf (-36)) (.leaf (-37)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 51 (.branch 42 (.leaf (-37)) (.branch 50 (.leaf (-35)) (.leaf (-28)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_308_5884 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (8))) (.branch 46 (.leaf (5)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5884
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-10)) (.branch 40 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-45))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 45 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.branch 53 (.leaf (-9)) (.leaf (-6))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 40 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 31 (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-45)) (.leaf (-44))) (.branch 12 (.leaf (-43)) (.branch 13 (.leaf (-42)) (.leaf (-41))))) (.branch 17 (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38)))) (.branch 18 (.leaf (-37)) (.branch 19 (.leaf (-36)) (.leaf (-35)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-34)) (.leaf (-33))) (.branch 23 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30))))) (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 29 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-24))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_308_5885 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (5))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (7)) (.leaf (4)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (5)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (8))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5885
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-43))),
  (.branch 29 (.leaf (0)) (.leaf (-25))),
  (.branch 47 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 47 (.branch 42 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-43)) (.leaf (-42))) (.branch 14 (.leaf (-41)) (.branch 15 (.leaf (-40)) (.leaf (-39))))) (.branch 18 (.branch 17 (.leaf (-38)) (.leaf (-37))) (.branch 19 (.leaf (-36)) (.branch 20 (.leaf (-35)) (.leaf (-34)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29))))) (.branch 29 (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-27)) (.leaf (-26)))) (.branch 30 (.leaf (-25)) (.branch 31 (.leaf (-24)) (.leaf (-23))))))) (.branch 43 (.branch 37 (.branch 34 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-20)) (.branch 36 (.leaf (-19)) (.leaf (-18))))) (.branch 40 (.branch 38 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 30 (.leaf (-25)) (.branch 31 (.leaf (-24)) (.leaf (-23)))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20))))) (.branch 38 (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 39 (.leaf (-16)) (.branch 40 (.leaf (-15)) (.leaf (-14)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308_5886 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (3))) (.branch 26 (.leaf (2)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (5))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (8)) (.leaf (3))) (.branch 53 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5886
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 48 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-30))),
  (.branch 51 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 37 (.leaf (-9)) (.branch 48 (.leaf (-8)) (.leaf (-5)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 31 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8)))) (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 46 (.branch 42 (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 31 (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 29 (.branch 28 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_308_5887 : CycleWitness 9 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (8)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (4))) (.branch 26 (.leaf (3)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (8)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (4)) (.leaf (7))))) (.branch 50 (.branch 48 (.leaf (8)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (6))) (.branch 53 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5887
  counts := ![(.branch 23 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-25)))) (.branch 41 (.branch 27 (.leaf (-29)) (.leaf (-33))) (.branch 45 (.leaf (-35)) (.leaf (-39))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 39 (.leaf (-14)) (.branch 44 (.leaf (-16)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 46 (.leaf (-39)) (.leaf (-40)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 30 (.leaf (-6)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 51 (.branch 46 (.leaf (-39)) (.leaf (-38))) (.branch 52 (.leaf (-33)) (.branch 53 (.leaf (-28)) (.leaf (-23))))),
  (.branch 52 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 53 (.leaf (-15)) (.leaf (-12)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-40)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.branch 31 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-6)))) (.branch 45 (.leaf (-4)) (.branch 46 (.leaf (-2)) (.leaf (0))))),
  (.branch 25 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 39 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-5))))),
  (.branch 50 (.branch 48 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))) (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.branch 30 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_308 : Fin 55 → CycleWitness 9 := ![witnessP9_308_5833, witnessP9_308_5834, witnessP9_308_5835, witnessP9_308_5836, witnessP9_308_5837, witnessP9_308_5838, witnessP9_308_5839, witnessP9_308_5840, witnessP9_308_5841, witnessP9_308_5842, witnessP9_308_5843, witnessP9_308_5844, witnessP9_308_5845, witnessP9_308_5846, witnessP9_308_5847, witnessP9_308_5848, witnessP9_308_5849, witnessP9_308_5850, witnessP9_308_5851, witnessP9_308_5852, witnessP9_308_5853, witnessP9_308_5854, witnessP9_308_5855, witnessP9_308_5856, witnessP9_308_5857, witnessP9_308_5858, witnessP9_308_5859, witnessP9_308_5860, witnessP9_308_5861, witnessP9_308_5862, witnessP9_308_5863, witnessP9_308_5864, witnessP9_308_5865, witnessP9_308_5866, witnessP9_308_5867, witnessP9_308_5868, witnessP9_308_5869, witnessP9_308_5870, witnessP9_308_5871, witnessP9_308_5872, witnessP9_308_5873, witnessP9_308_5874, witnessP9_308_5875, witnessP9_308_5876, witnessP9_308_5877, witnessP9_308_5878, witnessP9_308_5879, witnessP9_308_5880, witnessP9_308_5881, witnessP9_308_5882, witnessP9_308_5883, witnessP9_308_5884, witnessP9_308_5885, witnessP9_308_5886, witnessP9_308_5887]
end RealPinwheel.FiveSixths


