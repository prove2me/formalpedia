-- Prove2me | Definitions.Def_LL_Burst9MatrixC1_Params
-- name    : LL_Burst9MatrixC1_Params
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:54:45.012625+00:00
-- url     : https://prove2.me/theorems/55c1e8c6-ac5f-45f1-9974-d8d11538608c
-- title:
--   Kernel parameters $s, s', \kappa_1, \kappa_2, \kappa_3$
-- statement:
--   A record of five real numbers, the fields s, sp, k1, k2, k3, standing for Wu's parameters $s$, $s'$, $\kappa_1$, $\kappa_2$, $\kappa_3$ in Propositions 3 and 4. The structure imposes no constraints; admissibility is a separate predicate.

import Mathlib

namespace LL_Burst9MatrixC1

noncomputable section

open Real Set MeasureTheory
open scoped Classical

structure Params where
  s : ℝ
  sp : ℝ
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ

end

end LL_Burst9MatrixC1


