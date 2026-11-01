-- Prove2me | Definitions.Def_OLPDual_IsDualOptimal
-- name    : OLPDual_IsDualOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:18.808797+00:00
-- url     : https://prove2.me/theorems/b1b3e99d-5135-4a15-9a28-f978087da683
-- title:
--   The dual LP (3) and the objective of problem (5)
-- statement:
--   Given a sample $(a_j,r_j)_{j\le n}$ and a capacity vector $b\in\mathbb R^m$, the dual of the offline linear program is
--
--   $$
--   \min\ \sum_{i=1}^m b_ip_i+\sum_{j=1}^n y_j\quad\text{s.t.}\quad\sum_{i=1}^m a_{ij}p_i+y_j\ge r_j\ (j\le n),\qquad p_i,y_j\ge 0\ \text{for all }i,j. \tag{3}
--   $$
--
--   Substituting the smallest feasible $y_j$ gives the equivalent problem
--
--   $$
--   \min\ \sum_{i=1}^m b_ip_i+\sum_{j=1}^n\Bigl(r_j-\sum_{i=1}^m a_{ij}p_i\Bigr)^+\quad\text{s.t.}\quad p_i\ge 0. \tag{5}
--   $$
--
--   This module defines the feasible set and objective of (3), the predicate that $(p,y)$ is optimal for (3), and the objective of (5). They are used only in Proposition 1 (a), which connects the dual LP with the function $f_n$ of the rest of the paper.
--
--   **Formalization Note** Optimality is the plain statement that $(p,y)$ is feasible and no feasible point has a smaller objective value.
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), §3, (3) p.7, (5) p.8

import Mathlib
import Definitions.Def_OLPDual_Model

open scoped RealInnerProductSpace

namespace OLPDual

/-- The objective of problem (5), `Σ_i b_i p_i + Σ_j (r_j − a_jᵀp)⁺`,
Li–Ye, arXiv:1909.05499v5, p.8 (PDF 8). -/
noncomputable def obj5 {m n : ℕ} (b : E m) (ω : Sample m n) (p : E m) : ℝ :=
  ⟪b, p⟫ + ∑ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0

/-- Feasibility in the dual LP (3), Li–Ye, arXiv:1909.05499v5, p.7 (PDF 7):
`Σ_i a_ij p_i + y_j ≥ r_j` for every `j`, and `p_i, y_j ≥ 0`. -/
def DualFeasible {m n : ℕ} (ω : Sample m n) (p : E m) (y : Fin n → ℝ) : Prop :=
  (∀ j, ⟪(ω j).1, p⟫ + y j ≥ (ω j).2) ∧ (∀ i, 0 ≤ p i) ∧ ∀ j, 0 ≤ y j

/-- The objective `Σ_i b_i p_i + Σ_j y_j` of the dual LP (3), Li–Ye, arXiv:1909.05499v5, p.7
(PDF 7). -/
noncomputable def dualObj {m n : ℕ} (b p : E m) (y : Fin n → ℝ) : ℝ :=
  ⟪b, p⟫ + ∑ j, y j

/-- `(p, y)` is an optimal solution of the dual LP (3), Li–Ye, arXiv:1909.05499v5, p.7 (PDF 7):
it is feasible and has the least objective value among feasible points. -/
def IsDualOptimal {m n : ℕ} (b : E m) (ω : Sample m n) (p : E m) (y : Fin n → ℝ) : Prop :=
  DualFeasible ω p y ∧ ∀ p' y', DualFeasible ω p' y' → dualObj b p y ≤ dualObj b p' y'

end OLPDual


