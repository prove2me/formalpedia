-- Prove2me | Definitions.Def_SDDiP_LagCut_MixedIntegerPolyhedral
-- name    : SDDiP_LagCut_MixedIntegerPolyhedral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:19.252025+00:00
-- url     : https://prove2.me/theorems/dac56b5e-af1b-435e-8044-274aa02f2bd7
-- title:
--   Mixed integer polyhedral sets in $\mathbb R^n$ (assumption (A1))
-- statement:
--   A set $S \subseteq \mathbb R^n$ is **mixed integer polyhedral** if it is the set of integer-constrained points of a polyhedron: there are finitely many linear inequalities, given by a matrix $A \in \mathbb R^{m\times n}$ and a vector $b \in \mathbb R^m$, and an index set $J \subseteq \{1,\dots,n\}$ such that
--
--   $$S = \{\, w \in \mathbb R^n : A w \ge b,\ w_j \in \mathbb Z \ \text{for all } j \in J \,\}.$$
--
--   This is the class of constraint sets of mixed integer linear programs. Assumption (A1) of Zou, Ahmed and Sun requires every nodal constraint set $X_n$ of the multistage stochastic integer program to be a nonempty compact set of this kind.
--
--   **Formalization Note** The inequalities are written row by row, $b_r \le \sum_j A_{rj} w_j$; an equality constraint is a pair of opposite inequalities. The definition is stated on $\mathbb R^n$ = `Fin n → ℝ`; a set in a product space is mixed integer polyhedral when its image under the coordinate concatenation is.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 467, §2, assumption (A1)

import Mathlib

namespace SDDiP.LagCut

/-- A **mixed integer polyhedral set** in `ℝⁿ` (Zou, Ahmed, Sun, *Stochastic dual dynamic integer
programming*, Math. Program. 175 (2019), §2, assumption (A1), p. 467): the points of a polyhedron
`{w | A w ≥ b}` given by finitely many linear inequalities whose coordinates in a fixed index set `J`
are integers. -/
def IsMixedIntegerPolyhedral {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (J : Finset (Fin n)),
    S = {w | (∀ r, b r ≤ A r ⬝ᵥ w) ∧ ∀ j ∈ J, ∃ k : ℤ, w j = (k : ℝ)}

end SDDiP.LagCut


