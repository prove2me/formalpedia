-- Prove2me | Definitions.Def_SteuerChoo_Lexico_IsIdealVector
-- name    : SteuerChoo_Lexico_IsIdealVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:49:43.882562+00:00
-- url     : https://prove2.me/theorems/48b13ee5-bc69-409d-a1f1-59addef2b534
-- title:
--   The ideal criterion vector $z^*$ with its $\varepsilon$-rule
-- statement:
--   Let $Z\subseteq\mathbb R^k$ be the set of feasible criterion vectors and $N$ its nondominated set. A vector $z\in Z$ **maximizes the $i$-th objective** if $w_i\le z_i$ for every $w\in Z$.
--
--   A vector $z^*\in\mathbb R^k$ is an **ideal criterion vector** for $Z$ if
--   $$
--   z^*_i=\max\{z_i \mid z\in Z\}+\varepsilon_i,\qquad i=1,\dots,k,
--   $$
--   where every maximum is attained, a given $\varepsilon_i\ge 0$ ($\varepsilon_i=0$ is permissible), unless
--
--   1. there is more than one nondominated criterion vector that maximizes the $i$-th objective, or
--   2. the only nondominated criterion vector that maximizes the $i$-th objective also maximizes one of the other objectives,
--
--   in which case $\varepsilon_i$ must be strictly positive.
--
--   The ideal vector is the reference point from which every weighted Tchebycheff distance in the paper is measured. The $\varepsilon$-rule allows $z^*$ to touch the criterion set in a coordinate, but only where a single nondominated vector attains that coordinate's maximum and attains no other coordinate's maximum.
--
--   **Formalization Note** `MaximizesObj Z i z`, `CondI Z i` (condition 1) and `CondII Z i` (condition 2) are separate definitions; `IsIdealVector Z zstar` asserts the existence of the $\varepsilon$ vector with the three properties. The paper writes $\max\{f_i(x)\mid x\in S\}$; with $S$ eliminated this is the maximum of $z_i$ over $Z$, and its attainment (implicit in the paper's "max") is part of the definition.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 327, §2, definition of the ideal criterion vector z*, conditions (i)-(ii)

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_nondominated

namespace SteuerChoo.Lexico

/-- `z ∈ Z` maximizes the `i`-th objective over `Z`. -/
def MaximizesObj {k : ℕ} (Z : Set (Fin k → ℝ)) (i : Fin k) (z : Fin k → ℝ) : Prop :=
  z ∈ Z ∧ ∀ w ∈ Z, w i ≤ z i

/-- Condition (i) of §2, p. 327: there is more than one nondominated criterion
vector that maximizes the `i`-th objective. -/
def CondI {k : ℕ} (Z : Set (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, ∃ w ∈ nondominated Z, z ≠ w ∧ MaximizesObj Z i z ∧ MaximizesObj Z i w

/-- Condition (ii) of §2, p. 327: the only nondominated criterion vector that
maximizes the `i`-th objective also maximizes one of the other objectives. -/
def CondII {k : ℕ} (Z : Set (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, MaximizesObj Z i z ∧
    (∀ w ∈ nondominated Z, MaximizesObj Z i w → w = z) ∧
    ∃ j, j ≠ i ∧ MaximizesObj Z j z

/-- `zstar` is an ideal criterion vector for `Z` (§2, p. 327):
`zstar i = max {z i | z ∈ Z} + ε i` with every maximum attained, `ε i ≥ 0`,
and `ε i > 0` whenever condition (i) or (ii) holds for objective `i`. -/
def IsIdealVector {k : ℕ} (Z : Set (Fin k → ℝ)) (zstar : Fin k → ℝ) : Prop :=
  ∃ ε : Fin k → ℝ, (∀ i, 0 ≤ ε i) ∧
    (∀ i, ∃ z, MaximizesObj Z i z ∧ zstar i = z i + ε i) ∧
    ∀ i, (CondI Z i ∨ CondII Z i) → 0 < ε i

end SteuerChoo.Lexico


