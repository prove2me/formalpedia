-- Prove2me | Definitions.Def_Max3CutHard_WInst
-- name    : Max3CutHard_WInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:40.853813+00:00
-- url     : https://prove2.me/theorems/83ba914d-9517-495d-aa49-dc53c4898560
-- title:
--   A weighted role-separated instance $\Phi$ of 3Lin($\mathbb Z_3$)
-- statement:
--   A **role-separated instance** $\Phi$ of 3Lin($\mathbb Z_3$) consists of disjoint variable sets $U$ and $W$ and a collection of equations $e$ of the form $u_e+w_e+w'_e=t_e$, each carrying a weight $\lambda_e$.
--
--   The source requires $\lambda_e\ge0$ with $\sum_e\lambda_e=1$; this condition is the separate predicate *is a weighting*.
--
--   **Formalization Note** The collection is a list of pairs $(e,\lambda_e)$, so an equation may occur more than once.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_Eqn

namespace Max3CutHard

/-- **A weighted role-separated instance `Φ` of 3Lin(ℤ₃).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's
equations, p.4: "A role-separated instance `Φ` of 3Lin(ℤ₃) consists of disjoint sets `U` and `W` of
variables and a collection of equations `e` … and weights `λ_e ≥ 0` summing to 1."

**Formalization Note.** The collection is a list of pairs `(e, λ_e)` (repetitions allowed); the
weight conditions are the separate predicate `WInst.IsWeighting`. -/
structure WInst (U W : Type) where
  /-- the equations with their weights `λ_e` -/
  eqs : List (Eqn U W × ℝ)

end Max3CutHard


