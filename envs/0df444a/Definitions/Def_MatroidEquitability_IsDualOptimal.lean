-- Prove2me | Definitions.Def_MatroidEquitability_IsDualOptimal
-- name    : MatroidEquitability_IsDualOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:43.093564+00:00
-- url     : https://prove2.me/theorems/c328ab98-f990-40aa-8f3e-78ffc03c57ce
-- title:
--   Optimal solution of the dual of the gap linear program
-- statement:
--   The dual of the gap linear program is
--
--   $$
--   \min\ \sum_{e\in E}x_e\quad\text{s.t.}\quad\sum_{B\in\mathcal F^+,\,D\in\mathcal F^-}\lambda_{B,D}(\mathbf 1_B-\mathbf 1_D)\le x,\qquad\sum_{B\in\mathcal F^+,\,D\in\mathcal F^-}\lambda_{B,D}=1,\qquad x\ge 0,\quad\lambda\ge 0 .
--   $$
--
--   The pair $(\lambda,x)$ is **feasible** if it satisfies the constraints and **optimal** if, moreover, no feasible pair has a smaller objective value. The multipliers $\lambda$ form a probability distribution on $\mathcal F^+\times\mathcal F^-$.
--
--   **Formalization Note** The vector inequality and $x\ge 0$ are stated coordinatewise on $E$, and $\lambda\ge 0$ on $\mathcal F^+\times\mathcal F^-$.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_dualVector

namespace MatroidEquitability

/-- Feasibility for the dual of the linear program of the proof of Theorem 2: `λ ≥ 0`,
`Σ_{B,D} λ_{B,D} = 1`, `x ≥ 0` and `Σ_{B,D} λ_{B,D} (1_B − 1_D) ≤ x` (printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)). -/
def IsDualFeasible {α : Type*} (E : Set α) (Fp Fm : Finset (Set α))
    (lam : Set α → Set α → ℝ) (x : α → ℝ) : Prop :=
  (∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D) ∧ ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1 ∧
    ∀ e ∈ E, 0 ≤ x e ∧ dualVector Fp Fm lam e ≤ x e

/-- `(λ, x)` is an optimal solution of the dual
`min Σ_{e∈E} x_e` s.t. `Σ_{B,D} λ_{B,D} (1_B − 1_D) ≤ x`, `Σ_{B,D} λ_{B,D} = 1`, `x ≥ 0`, `λ ≥ 0`
(proof of Theorem 2, printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)). -/
def IsDualOptimal {α : Type*} (E : Set α) (Fp Fm : Finset (Set α))
    (lam : Set α → Set α → ℝ) (x : α → ℝ) : Prop :=
  IsDualFeasible E Fp Fm lam x ∧
    ∀ lam' x', IsDualFeasible E Fp Fm lam' x' → setWeight x E ≤ setWeight x' E

end MatroidEquitability


