-- Prove2me | Definitions.Def_PWDB_Solvable
-- name    : PWDB_Solvable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:14.532594+00:00
-- url     : https://prove2.me/theorems/3a00d4fc-ef92-4730-b2e0-c86baf3dfded
-- title:
--   Solvable minimization and maximization problems
-- statement:
--   For a problem with feasible region $\mathcal F$ and objective $\varphi$: a minimization problem is **solvable** if $\mathcal F = \emptyset$ or some $x \in \mathcal F$ satisfies $\varphi(x) \le \varphi(y)$ for all $y \in \mathcal F$; a maximization problem likewise with $\varphi(y) \le \varphi(x)$.
--
--   As on p.40, a feasible point satisfies all constraints and has objective value other than $+\infty$ (minimization) or $-\infty$ (maximization), and "an infeasible optimization problem is solved by any (necessarily infeasible) solution".
--
--   **Formalization Note** The feasible region is passed in; every problem of the mission defines it with the exclusion of the bad objective value.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Appendix A, p.40

import Mathlib

namespace PWDB

/-- **Solvable minimization problem** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Appendix A,
p.40): "A feasible optimization problem is solvable if its optimal value is attained by a feasible
solution, whereas an infeasible optimization problem is solved by any (necessarily infeasible)
solution."

`SolvableMin Feas obj` says: the feasible region `Feas` is empty, or some feasible point minimizes
`obj` over `Feas`.

**Formalization Note** `Feas` is the feasible region in the paper's sense (p.40): the points that
satisfy all constraints and have objective value other than `+∞`. The infeasible branch is part of
the definition, as on p.40. -/
def SolvableMin {α : Type*} (Feas : Set α) (obj : α → EReal) : Prop :=
  Feas = ∅ ∨ ∃ x ∈ Feas, ∀ y ∈ Feas, obj x ≤ obj y

/-- **Solvable maximization problem** (arXiv:2105.00760v2, Appendix A, p.40): the feasible region
is empty, or some feasible point maximizes `obj` over it. Feasibility of a point of a maximization
problem excludes the objective value `−∞` (p.40). -/
def SolvableMax {α : Type*} (Feas : Set α) (obj : α → EReal) : Prop :=
  Feas = ∅ ∨ ∃ x ∈ Feas, ∀ y ∈ Feas, obj y ≤ obj x

end PWDB


