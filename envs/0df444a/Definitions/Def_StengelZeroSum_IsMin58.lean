-- Prove2me | Definitions.Def_StengelZeroSum_IsMin58
-- name    : StengelZeroSum_IsMin58
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:45.344233+00:00
-- url     : https://prove2.me/theorems/9863a367-bb4b-4479-adf3-4cc91de1fbc8
-- title:
--   Minimizers of $w$ subject to (58)
-- statement:
--   A pair $(z^*,w^*)$ **minimizes $w$ subject to (58)** if it is feasible for (58) and $w^*\le w$ for every feasible $(z,w)$.
--
--   Theorem 8 is stated for such a minimizer, which in the paper is moreover basic (see the predicate of basicness for (58)).
--
--   **Formalization Note** Minimality is stated against every feasible point, so no infimum is involved.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 8, p.21

import Mathlib
import Definitions.Def_StengelZeroSum_Feasible58

namespace StengelZeroSum

/-- `(z, w)` is a feasible solution of (58) **that minimizes `w`**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 8,
p.21 ("a … feasible solution that minimizes w subject to (58)"): `(z, w)` is feasible for (58)
and `w ≤ w'` for every feasible `(z', w')`.

**Formalization Note** Minimality is stated against every feasible point, so no infimum is
taken. Basicness, which Theorem 8 also asks for, is the separate predicate `IsBasic58`. -/
def IsMin58 {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ) (d : ι → ℝ) (z : ι → ℝ) (w : ℝ) :
    Prop :=
  Feasible58 C d z w ∧ ∀ (z' : ι → ℝ) (w' : ℝ), Feasible58 C d z' w' → w ≤ w'

end StengelZeroSum


