-- Prove2me | Definitions.Def_BayesBAI_insertTwo
-- name    : BayesBAI_insertTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:56.721614+00:00
-- url     : https://prove2.me/theorems/8640c690-48fa-4ddb-ae95-b1c582739192
-- title:
--   Inserting coordinates $x,y$ at arms $i,j$
-- statement:
--   The vector of $\mathbb R^K$ with coordinates $x$ at $i$ and $y$ at $j$, for $i\ne j$, and the remaining coordinates given by $\nu$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1.1, p.2

import Mathlib

namespace BayesBAI

/-- The vector with coordinates `x` at `i` and `y` at `j`, the others from `ν`, for the conditional
density `h_ij(x, y | ν)` of Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, §1.1, p.2. Used for `i ≠ j`. -/
def insertTwo {K : ℕ} (i j : Fin K) (x y : ℝ) (ν : {k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) : Fin K → ℝ :=
  fun k => if h : k = i then x else if h' : k = j then y else ν ⟨k, h, h'⟩

end BayesBAI


