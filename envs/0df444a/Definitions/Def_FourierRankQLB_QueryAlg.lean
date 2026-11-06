-- Prove2me | Definitions.Def_FourierRankQLB_QueryAlg
-- name    : FourierRankQLB_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:21.570634+00:00
-- url     : https://prove2.me/theorems/201b965a-4fee-4511-8f59-80f4ab563878
-- title:
--   A $T$-query algorithm with a final POVM
-- statement:
--   A $T$-query algorithm of the form (15) with outcomes in a measurable space $X$: a query circuit together with a final POVM on $X$, all independent of the hidden matrix.
--
--   An optimizer has outcomes in $\mathbb R^n$, and a determinant predictor has outcomes in $\{-1,+1\}$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (15), p.16

import Mathlib
import Definitions.Def_FourierRankQLB_QueryCircuit
import Definitions.Def_FourierRankQLB_POVM

namespace FourierRankQLB

/-- A `T`-query algorithm (15) with outcomes in `X`: a query circuit and a final POVM on `X`, all
independent of the hidden matrix.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (15), p. 16. -/
structure QueryAlg (H X : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [MeasurableSpace X] extends QueryCircuit H where
  /-- The final measurement. -/
  meas : POVM X H

end FourierRankQLB


