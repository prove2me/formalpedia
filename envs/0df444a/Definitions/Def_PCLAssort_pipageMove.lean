-- Prove2me | Definitions.Def_PCLAssort_pipageMove
-- name    : PCLAssort_pipageMove
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:20.195258+00:00
-- url     : https://prove2.me/theorems/6deef475-e744-4215-aea1-69ab6eb81da7
-- title:
--   Pipage move along a pair of coordinates
-- statement:
--   For sizes $s$, a point $x$, two coordinates $i,j$ and a step $\epsilon$, the moved point is
--
--   $$
--   (x_1,\dots,x_i+\epsilon,\dots,x_j-\tfrac{s_i}{s_j}\epsilon,\dots,x_n).
--   $$
--
--   The move keeps $\sum_k s_k x_k$ unchanged. The function $\phi(x,i,j,\epsilon)$ of Definition 3 is $F$ evaluated at this point.
--
--   **Formalization Note** For $i=j$ the move changes nothing when $s_i\neq 0$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 3 and pipage rounding step 3, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- The point `(x_1, …, x_i + ε, …, x_j − (s_i/s_j) ε, …, x_n)` moved along the pipage direction of
the pair `(i, j)` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, Definition 3 and step 3 of pipage rounding, p.794). The function
`φ(x, i, j, ε)` of Definition 3 is `F (pipageMove s x i j ε)`.

**Formalization Note.** For `i = j` the move is `x_i + ε − ε = x_i` whenever `s_i ≠ 0`. -/
noncomputable def pipageMove {V : Type} [DecidableEq V] (s : V → ℝ) (x : V → ℝ) (i j : V) (ε : ℝ) :
    V → ℝ :=
  fun k => x k + (if k = i then ε else 0) - (if k = j then s i / s j * ε else 0)

end PCLAssort


