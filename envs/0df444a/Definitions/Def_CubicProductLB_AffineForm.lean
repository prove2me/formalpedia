-- Prove2me | Definitions.Def_CubicProductLB_AffineForm
-- name    : CubicProductLB_AffineForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:55.8432+00:00
-- url     : https://prove2.me/theorems/2c342b92-1ba8-4ad2-9421-31695937ece0
-- title:
--   Affine forms $A(x) = a_0 + \sum_j a_j x_j$ over $\mathbb F_3$
-- statement:
--   An **affine form** over $\mathbb F_3$ is an expression $A(x) = a_0 + \sum_j a_j x_j$, with a constant term and a coefficient vector. It may involve all $n$ variables.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 3, p.4

import Mathlib

namespace CubicProductLB

/-- An affine form `A(x) = a_0 + ∑_j a_j x_j` over `F_3`, as the pair `(a_0, a)`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 3, p.4). -/
abbrev AffineForm (n : ℕ) := ZMod 3 × (Fin n → ZMod 3)

/-- The value of an affine form at a point. -/
def AffineForm.eval {n : ℕ} (A : AffineForm n) (x : Fin n → ZMod 3) : ZMod 3 :=
  A.1 + ∑ i, A.2 i * x i

end CubicProductLB


