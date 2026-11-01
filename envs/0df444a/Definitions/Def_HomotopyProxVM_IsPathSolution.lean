-- Prove2me | Definitions.Def_HomotopyProxVM_IsPathSolution
-- name    : HomotopyProxVM_IsPathSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:35.095045+00:00
-- url     : https://prove2.me/theorems/ebfeb949-94c0-4264-9640-e7aa5e3bd949
-- title:
--   A solution $x^*_\tau$ of the parametrized problem (8)
-- statement:
--   A point $y$ is a **solution of the parametrized problem** (8) at $\tau$ if it minimizes
--
--   $$
--   F_\tau(x):=f_\tau(x)+g(x)
--   $$
--
--   over $\mathbb R^p$. The solutions $x^*_\tau$ form the homotopy path, and $x^*_1$ solves the original problem (1).
--
--   **Formalization Note** $g$ is given by its domain $D$ and its values on $D$, so a minimizer lies in $D$ and is compared with the points of $D$. This is a predicate, not a chosen minimizer: existence and uniqueness are claims of `path_solution` and `theorem_4`.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §3.1, (8), p.6

import Mathlib
import Definitions.Def_HomotopyProxVM_parametrizedFn

namespace HomotopyProxVM

/-- `y` is a solution `x*_τ` of the parametrized problem (8),
`min_x { F_τ(x) := f_τ(x) + g(x) }` (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §3.1, (8), p.6).

**Formalization Note.** `g` is encoded by its domain `D` and its values on `D`, so a minimizer lies
in `D` and is compared with the points of `D`. This is a predicate, not a choice of minimizer: the
existence and uniqueness of `x*_τ` are claims of the mission (`path_solution`, `theorem_4`). -/
def IsPathSolution {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin p)) (τ : ℝ) (y : EuclideanSpace ℝ (Fin p)) : Prop :=
  y ∈ D ∧ ∀ w ∈ D, parametrizedFn f ξ τ y + g y ≤ parametrizedFn f ξ τ w + g w

end HomotopyProxVM


