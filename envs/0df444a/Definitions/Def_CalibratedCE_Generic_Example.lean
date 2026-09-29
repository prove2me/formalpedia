-- Prove2me | Definitions.Def_CalibratedCE_Generic_Example
-- name    : CalibratedCE_Generic_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:02:44.806986+00:00
-- url     : https://prove2.me/theorems/96ba2eef-d84a-49e1-868e-75fc22c53c09
-- title:
--   The $3\times 3$ game of p. 48 and two of its distributions
-- statement:
--   The game of p. 48, with Row's strategies $A, B, C$ and Column's strategies $1, 2, 3$ (entries Row\Col):
--
--   | | 1 | 2 | 3 |
--   |---|---|---|---|
--   | A | 2\2 | 0\3 | 0\1 |
--   | B | 2\2 | 0\1 | 0\3 |
--   | C | 2\0 | 1\1 | 1\0 |
--
--   So Row's payoff matrix is $u_1 = \begin{pmatrix}2&0&0\\2&0&0\\2&1&1\end{pmatrix}$ and Column's is $u_2 = \begin{pmatrix}2&3&1\\2&1&3\\0&1&0\end{pmatrix}$.
--
--   $D_0$ is the distribution in which "Row randomizes between A and B (with equal probability) and Col plays 1": $D_0(A,1) = D_0(B,1) = 1/2$. $\delta_{(C,2)}$ is the distribution "which puts all its weight on point $(C, 2)$".
--
--   **Formalization Note** $A, B, C$ are indices $0, 1, 2$ and columns $1, 2, 3$ are indices $0, 1, 2$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 48, example after the proof of Theorem 2

import Mathlib

namespace CalibratedCE.Generic

/-- Row's payoffs in the 3 × 3 game of Foster–Vohra p. 48. Rows `A, B, C` are `0, 1, 2`,
columns `1, 2, 3` are `0, 1, 2`. -/
def exU₁ : Fin 3 → Fin 3 → ℝ := ![![2, 0, 0], ![2, 0, 0], ![2, 1, 1]]

/-- Column's payoffs in the 3 × 3 game of Foster–Vohra p. 48. -/
def exU₂ : Fin 3 → Fin 3 → ℝ := ![![2, 3, 1], ![2, 1, 3], ![0, 1, 0]]

/-- Row randomizes between `A` and `B` with equal probability and Column plays `1`. -/
noncomputable def exD₀ : Fin 3 → Fin 3 → ℝ :=
  fun a b => if b = 0 ∧ (a = 0 ∨ a = 1) then 1 / 2 else 0

/-- The point mass on `(C, 2)`. -/
def exDelta : Fin 3 → Fin 3 → ℝ :=
  fun a b => if a = 2 ∧ b = 1 then 1 else 0

end CalibratedCE.Generic


