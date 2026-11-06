-- Prove2me | Definitions.Def_HOTrap_PolyLE
-- name    : HOTrap_PolyLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:54.948139+00:00
-- url     : https://prove2.me/theorems/40db38c9-335c-4ae2-9f35-d9c67e01ca5d
-- title:
--   The polynomial space $\Pi^d_p$
-- statement:
--   $\Pi^d_p$ is the space of real polynomials of total degree at most $p$ in $d$ variables, viewed as functions on $\mathbb R^d$.
--
--   It is the interpolation space of Proposition A.5 and Corollary A.8.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix A, Notation, p.53

import Mathlib
import Definitions.Def_HOTrap_polyEval

namespace HOTrap

/-- **The polynomial space `Π^d_p`**: real polynomials of total degree at most `p` in `d` variables,
as functions on `ℝ^d`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix A, Notation, p.53. -/
noncomputable def PolyLE (d p : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ) :=
  (MvPolynomial.restrictTotalDegree (Fin d) ℝ p).map (polyEval d)

end HOTrap


