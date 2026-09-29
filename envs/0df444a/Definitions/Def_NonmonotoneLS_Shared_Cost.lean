-- Prove2me | Definitions.Def_NonmonotoneLS_Shared_Cost
-- name    : NonmonotoneLS_Shared_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:14:37.124189+00:00
-- url     : https://prove2.me/theorems/e1b7cc7f-42a6-48a7-9225-2563974c169a
-- title:
--   The weights $Q_k$, reference values $C_k$ and averages $A_k$ of the nonmonotone line search
-- statement:
--   Let $x_0, x_1, x_2, \dots$ be a sequence of points, $f$ a real-valued function and $\eta_0, \eta_1, \dots$ real weights. The **weights** $Q_k$ and **reference values** $C_k$ of the nonmonotone line search are defined by the cost update (1.6):
--
--   $$Q_0 = 1,\quad Q_{k+1} = \eta_k Q_k + 1, \qquad C_0 = f(x_0),\quad C_{k+1} = \frac{\eta_k Q_k C_k + f(x_{k+1})}{Q_{k+1}}.$$
--
--   The **average function value** is
--
--   $$A_k = \frac{1}{k+1} \sum_{i=0}^{k} f(x_i).$$
--
--   When $\eta_k \in [0,1]$, $C_{k+1}$ is a convex combination of $C_k$ and $f(x_{k+1})$, so $C_k$ is a convex combination of $f(x_0), \dots, f(x_k)$; the choice $\eta_k = 0$ gives $C_k = f(x_k)$ (the monotone line search) and $\eta_k = 1$ gives $C_k = A_k$.
--
--   It serves chunk 01-global-convergence (p. 1044, Eq. (1.6) and $A_k$; used by Lemma 1.1 and Eq. (1.8) p. 1045, Eqs. (2.8)–(2.9) p. 1047, Eqs. (2.14)–(2.15) p. 1048) and chunk 02-r-linear-convergence (p. 1044, Eq. (1.6) and $A_k$; used by Lemma 1.1 p. 1045, Eq. (2.15) p. 1048, Eqs. (3.6) and (3.8) and the proof of Theorem 3.1 p. 1050, Theorem 3.2 p. 1051).
--
--   **Formalization Note.** $Q$ and $C$ are defined by structural recursion on $k$ as functions of the whole sequences $(x_k)$ and $(\eta_k)$. For negative weights $Q_{k+1}$ could vanish and Lean's division by zero would return $0$; every run of the algorithm has $\eta_k \ge 0$, hence $Q_k \ge 1$, so this never occurs for the statements of the mission.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1044, Eq. (1.6) and the definition of A_k

import Mathlib

namespace NonmonotoneLS.Shared

/-- The weights `Q_k` of the nonmonotone line search, Eq. (1.6):
`Q_0 = 1` and `Q_{k+1} = η_k Q_k + 1`. -/
def costQ (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => η k * costQ η k + 1

/-- The reference values `C_k` of the nonmonotone line search, Eq. (1.6), along the iterates `x`:
`C_0 = f(x_0)` and `C_{k+1} = (η_k Q_k C_k + f(x_{k+1})) / Q_{k+1}`. -/
noncomputable def costC {E : Type*} (f : E → ℝ) (x : ℕ → E) (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => f (x 0)
  | k + 1 => (η k * costQ η k * costC f x η k + f (x (k + 1))) / costQ η (k + 1)

/-- The average function value `A_k = (1/(k+1)) ∑_{i=0}^{k} f(x_i)` (p. 1044). -/
noncomputable def avgA {E : Type*} (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), f (x i)) / ((k : ℝ) + 1)

end NonmonotoneLS.Shared


