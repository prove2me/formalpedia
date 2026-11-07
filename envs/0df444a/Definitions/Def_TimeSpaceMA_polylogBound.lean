-- Prove2me | Definitions.Def_TimeSpaceMA_polylogBound
-- name    : TimeSpaceMA_polylogBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:09.983206+00:00
-- url     : https://prove2.me/theorems/48d47adc-0361-4f46-b39a-64b6f7904aa9
-- title:
--   The bound $\mathrm{polylog}(n)=C(\log_2 n+2)^K$
-- statement:
--   The function $n\mapsto C(\log_2 n+2)^K$. In Lemmas A.3 and 3.10 one $C$ and one $K$ serve all $n$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma A.3, p.33; Lemma 3.10, p.12

import Mathlib

namespace TimeSpaceMA

/-- The bound `polylog(n)` of Lemmas A.3 and 3.10: `C · (log₂ n + 2)^K`, for one `C` and `K` that do not
depend on `n`. -/
noncomputable def polylogBound (C : ℝ) (K : ℕ) (n : ℕ) : ℝ :=
  C * (Real.logb 2 n + 2) ^ K

end TimeSpaceMA


