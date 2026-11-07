-- Prove2me | Definitions.Def_QuasiStrictNE_PLFPData_D
-- name    : QuasiStrictNE_PLFPData_D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:14.003032+00:00
-- url     : https://prove2.me/theorems/8f309de0-57ee-46ee-b3e0-44a1b1fd298e
-- title:
--   Domain $D_I$ of a piecewise-linear fixed-point problem
-- statement:
--   $D_I$ is the polytope of points $x\in\mathbb R^{d_I}$ satisfying all inequalities $a^\top x\le b$ of the instance.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6.1, p.8

import Mathlib
import Definitions.Def_QuasiStrictNE_PLFPData

namespace QuasiStrictNE

/-- **The domain `D_I` of a piecewise-linear fixed-point problem** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 6.1, p.8: "DI is a
polytope defined by a set of linear inequalities").

`Φ.D I` is the set of `x ∈ ℝ^{dim I}` satisfying every inequality `a⊤x ≤ b` of `Φ.ineqs I`. -/
def PLFPData.D (Φ : PLFPData) (I : List Bool) : Set (Fin (Φ.dim I) → ℝ) :=
  {x | ∀ ab ∈ Φ.ineqs I, ∑ i, (ab.1 i : ℝ) * x i ≤ (ab.2 : ℝ)}

end QuasiStrictNE


