-- Prove2me | Definitions.Def_KallMayerSLP_KKT_feasibleSet
-- name    : KallMayerSLP_KKT_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:36.626509+00:00
-- url     : https://prove2.me/theorems/d4a52068-610b-4ba8-be6a-a60b4675f902
-- title:
--   Feasible set $\mathcal B$ of the convex program (3.1)
-- statement:
--   For constraint functions $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$, the **feasible set** of the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le 0,\ i=1,\dots,m \tag{3.1}
--   $$
--   is
--   $$
--   \mathcal B:=\{x\in\mathbb R^n\mid g_i(x)\le 0,\ i=1,\dots,m\}.
--   $$
--
--   It is the set over which (3.1) minimizes; every optimality statement of the section refers to it.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and the constraints are indexed by `Fin m` (0-based).
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.61 (PDF 72), definition of B

import Mathlib

namespace KallMayerSLP.KKT

/-- **The feasible set `𝓑` of the convex program (3.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.61 (PDF 72):
"`𝓑 := {x | gᵢ(x) ≤ 0, i = 1, ⋯, m}`", the feasible set of
`min f(x) s.t. gᵢ(x) ≤ 0, i = 1, ⋯, m` (3.1).

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; the constraints are indexed by
`Fin m` (the book's `i = 1, …, m` is `i = 0, …, m - 1`). -/
def feasibleSet {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, g i x ≤ 0}

end KallMayerSLP.KKT


