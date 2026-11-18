-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_043
-- name    : RealPinwheel_FiveSixths_WitnessD7_043
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:49:19.91972+00:00
-- url     : https://prove2.me/theorems/4f2a4741-9430-4e53-8006-1d5778c297d5
-- title:
--   Exact witness block D7_043
-- statement:
--   These exact witnesses represent words 627 through 649 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 627–649; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_043_626 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_626
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-22)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 13 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 34 (.leaf (-3)) (.leaf (0))),
  (.branch 39 (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1))]
def witnessD7_043_627 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (4)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (5)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (4)) (.leaf (5))))))))
  code := certificateD7_627
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-16))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 38 (.leaf (-13)) (.leaf (-14))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.branch 40 (.leaf (-7)) (.leaf (-8))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 20 (.leaf (-24)) (.leaf (-26)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 40 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 41 (.leaf (-8)) (.leaf (-6))),
  (.branch 39 (.branch 21 (.leaf (-26)) (.branch 38 (.leaf (-25)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.leaf (0)),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_043_628 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (5)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (1))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_628
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))) (.branch 17 (.leaf (-15)) (.branch 38 (.leaf (-17)) (.leaf (-18))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-14))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_043_629 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_629
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 28 (.leaf (-11)) (.branch 38 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 12 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1))]
def witnessD7_043_630 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (5))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_630
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 26 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 39 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 38 (.branch 22 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_043_631 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (3)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_631
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.branch 17 (.leaf (-15)) (.leaf (-16))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 37 (.leaf (-8)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 40 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-3)),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_043_632 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (6)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_632
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 40 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_043_633 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_633
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.leaf (-8)) (.leaf (-7))),
  (.branch 39 (.branch 38 (.leaf (-10)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_043_634 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_634
  counts := ![(.branch 18 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 25 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-9)) (.leaf (-12)))),
  (.leaf (0))]
  high := ![(.branch 35 (.branch 26 (.leaf (-16)) (.leaf (-15))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (0))]
def witnessD7_043_635 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_635
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 35 (.leaf (-10)) (.leaf (-13)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 4 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 25 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (0)))),
  (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (-1))]
def witnessD7_043_636 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_636
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-5)) (.branch 34 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-27)) (.leaf (-28)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 38 (.leaf (-9)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.leaf (-8)) (.leaf (-7))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 29 (.leaf (-28)) (.branch 38 (.leaf (-25)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 8 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.leaf (-11)))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_043_637 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (4))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_637
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-27)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-12)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.leaf (-5)) (.leaf (-4))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 29 (.leaf (-28)) (.branch 38 (.leaf (-25)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_043_638 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (5)) (.leaf (2))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_638
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 40 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 22 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 36 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 33 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_043_639 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_639
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.branch 27 (.leaf (-7)) (.leaf (-9))))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_043_640 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (6)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_640
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-12)) (.leaf (-13)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 26 (.leaf (-4)) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 34 (.leaf (-13)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.leaf (-7)),
  (.branch 38 (.branch 25 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_043_641 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_641
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 27 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_043_642 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_642
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 25 (.leaf (-18)) (.leaf (-19)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 23 (.leaf (-8)) (.branch 27 (.leaf (-9)) (.leaf (-10))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 39 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-6))))),
  (.branch 28 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 33 (.branch 17 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_043_643 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_643
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))) (.branch 29 (.leaf (-7)) (.branch 34 (.leaf (-8)) (.leaf (-9))))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-27))),
  (.branch 36 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 40 (.branch 31 (.leaf (-18)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.leaf (-8)) (.leaf (-5))),
  (.branch 39 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 35 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-6)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 21 (.branch 18 (.branch 16 (.leaf (-27)) (.branch 17 (.leaf (-26)) (.leaf (-25)))) (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_043_644 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_644
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (-4))) (.branch 37 (.leaf (-10)) (.leaf (-15)))),
  (.leaf (0))]
  high := ![(.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-9))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 33 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11))))),
  (.leaf (0))]
def witnessD7_043_645 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_645
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-3)) (.leaf (0))),
  (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_043_646 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (4)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (2)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (4)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_646
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 16 (.leaf (-14)) (.branch 37 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.branch 30 (.leaf (-8)) (.leaf (-10))))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 39 (.branch 38 (.leaf (-17)) (.leaf (-14))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 40 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 29 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_043_647 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4)))))) (.branch 30 (.branch 26 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_647
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 13 (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))) (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.leaf (13)))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (16)))) (.branch 26 (.branch 25 (.leaf (17)) (.leaf (18))) (.branch 28 (.leaf (19)) (.leaf (20))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.leaf (24)))) (.branch 38 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 39 (.leaf (27)) (.leaf (28))))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_043_648 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2)))))) (.branch 30 (.branch 26 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_648
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 13 (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))) (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.leaf (13)))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (16)))) (.branch 26 (.branch 25 (.leaf (17)) (.leaf (18))) (.branch 28 (.leaf (19)) (.leaf (20))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.leaf (24)))) (.branch 38 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 39 (.leaf (27)) (.leaf (28))))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-36))),
  (.branch 24 (.leaf (0)) (.leaf (-16))),
  (.branch 34 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 22 (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-36)) (.leaf (-35))) (.branch 7 (.leaf (-34)) (.leaf (-33)))) (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_043 : Fin 23 → CycleWitness 7 := ![witnessD7_043_626, witnessD7_043_627, witnessD7_043_628, witnessD7_043_629, witnessD7_043_630, witnessD7_043_631, witnessD7_043_632, witnessD7_043_633, witnessD7_043_634, witnessD7_043_635, witnessD7_043_636, witnessD7_043_637, witnessD7_043_638, witnessD7_043_639, witnessD7_043_640, witnessD7_043_641, witnessD7_043_642, witnessD7_043_643, witnessD7_043_644, witnessD7_043_645, witnessD7_043_646, witnessD7_043_647, witnessD7_043_648]
end RealPinwheel.FiveSixths


