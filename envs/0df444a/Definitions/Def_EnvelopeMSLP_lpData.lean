-- Prove2me | Definitions.Def_EnvelopeMSLP_lpData
-- name    : EnvelopeMSLP_lpData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:50.19901+00:00
-- url     : https://prove2.me/theorems/f21240f8-10c2-46bd-90cb-bcbc3118259a
-- title:
--   The stacked data vector of an LP
-- statement:
--   The point of $\mathbb R^N$ with the entries of $D$, $b$ and $c$ at their positions in `LPIndex m n`.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.8

import Mathlib
import Definitions.Def_EnvelopeMSLP_LPIndex
open Matrix

namespace EnvelopeMSLP

/-- **The stacked data vector** of `(D, b, c)`. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.8. -/
def lpData {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    LPIndex m n → ℝ :=
  Sum.elim (fun ij => D ij.1 ij.2) (Sum.elim b c)

end EnvelopeMSLP


