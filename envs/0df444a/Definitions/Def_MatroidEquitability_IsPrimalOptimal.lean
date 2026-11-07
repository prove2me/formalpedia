-- Prove2me | Definitions.Def_MatroidEquitability_IsPrimalOptimal
-- name    : MatroidEquitability_IsPrimalOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:27.945269+00:00
-- url     : https://prove2.me/theorems/0dbceb86-e03b-4593-8a65-49cf01521ac7
-- title:
--   Optimal solution of the gap linear program of the proof of Theorem 2
-- statement:
--   For a finite set $E$ and finite families $\mathcal F^+,\mathcal F^-$ of subsets of $E$, consider the linear program
--
--   $$
--   \max\ \gamma\quad\text{s.t.}\quad u(B)-u(D)\ge\gamma\ \ \forall B\in\mathcal F^+,\,D\in\mathcal F^-,\qquad 0\le u_e\le 1\ \ \forall e\in E .
--   $$
--
--   The pair $(u,\gamma)$ is **feasible** if it satisfies the constraints and **optimal** if, moreover, no feasible pair has a larger value of $\gamma$. The program maximizes the gap between the two families of sets over all weight vectors in the unit cube.
--
--   **Formalization Note** The vector $u$ is a function on the whole type, constrained only on $E$.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight

namespace MatroidEquitability

/-- Feasibility for the linear program of the proof of Theorem 2: `0 ≤ u_e ≤ 1` for `e ∈ E`, and
`u(B) − u(D) ≥ γ` for all `B ∈ F⁺`, `D ∈ F⁻` (printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)). -/
def IsPrimalFeasible {α : Type*} (E : Set α) (Fp Fm : Finset (Set α)) (u : α → ℝ) (γ : ℝ) : Prop :=
  (∀ e ∈ E, 0 ≤ u e ∧ u e ≤ 1) ∧ ∀ B ∈ Fp, ∀ D ∈ Fm, γ ≤ setWeight u B - setWeight u D

/-- `(u, γ)` is an optimal solution of the linear program
`max γ` s.t. `u(B) − u(D) ≥ γ` for all `B ∈ F⁺`, `D ∈ F⁻`, and `0 ≤ u_e ≤ 1` for all `e ∈ E`
(proof of Theorem 2, printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The vector `u` is a function on all of `α`; only its values on `E` are
constrained, and the families are finite sets of subsets of `α`. -/
def IsPrimalOptimal {α : Type*} (E : Set α) (Fp Fm : Finset (Set α)) (u : α → ℝ) (γ : ℝ) : Prop :=
  IsPrimalFeasible E Fp Fm u γ ∧ ∀ u' γ', IsPrimalFeasible E Fp Fm u' γ' → γ' ≤ γ

end MatroidEquitability


