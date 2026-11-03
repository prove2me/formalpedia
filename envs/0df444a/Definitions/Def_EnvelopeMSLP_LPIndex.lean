-- Prove2me | Definitions.Def_EnvelopeMSLP_LPIndex
-- name    : EnvelopeMSLP_LPIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:49.948047+00:00
-- url     : https://prove2.me/theorems/4f3666e4-520d-4cdd-8789-732f37fde7cd
-- title:
--   Index set of the stacked data of an LP
-- statement:
--   The paper views the data of a linear program as a point of $\mathbb R^N$ by stacking all the vectors and columns. This definition is the index set of that point: the $mn$ entries of the matrix, the $m$ entries of the right-hand side and the $n$ entries of the objective.
--
--   **Formalization Note** $\mathbb R^N$ is `LPIndex m n → ℝ`, so no enumeration of the entries is chosen.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.8

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **Index set of the stacked data of a linear program.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.8: the data `(d, D, b)` is viewed
as a point of `ℝ^N` "by stacking all the vectors and columns". The entries are the matrix entries,
then the right-hand side, then the objective; `N = mn + m + n`.

**Formalization Note.** `ℝ^N` is `LPIndex m n → ℝ`, so no enumeration of the entries is chosen. -/
abbrev LPIndex (m n : ℕ) : Type := (Fin m × Fin n) ⊕ Fin m ⊕ Fin n

end EnvelopeMSLP


