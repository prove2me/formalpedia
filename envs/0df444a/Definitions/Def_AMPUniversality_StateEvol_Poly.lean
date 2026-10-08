-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_Poly
-- name    : AMPUniversality_StateEvol_Poly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:02.215022+00:00
-- url     : https://prove2.me/theorems/e3acd6f4-14ad-4837-a3fd-6653890ad53f
-- title:
--   Polynomial maps and Jacobians in coefficient form, (4.10)
-- statement:
--   A polynomial map $f:\mathbb R^q\to\mathbb R^q$ of degree at most $d$ is specified by real coefficients $c_{r,m}$, one for each output coordinate $r$ and multi-index $m$ with $0\le m_s\le d$ and $\sum_s m_s\le d$:
--
--   $$f_r(x)=\sum_{\sum_s m_s\le d}c_{r,m}\prod_s x_s^{m_s}.$$
--
--   The accompanying Jacobian gives the coordinate partial derivatives of this expression. This coefficient form permits random polynomial maps and makes the uniform coefficient bound in Definition 4 precise. The monomial helper uses arbitrary natural-number exponents.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 17, (4.10); p. 7, Definition 4(2)

import Mathlib

set_option autoImplicit false

namespace AMPUniversality.StateEvol

/-- Coordinate monomial, with natural-number exponents. -/
def monomial {q : ℕ} (m : Fin q → ℕ) (x : Fin q → ℝ) : ℝ :=
  ∏ s, x s ^ m s

/-- The coefficient form of a degree-at-most-`d` polynomial map (4.10). -/
def polyEval {q d : ℕ}
    (c : Fin q → (Fin q → Fin (d + 1)) → ℝ)
    (x : Fin q → ℝ) (r : Fin q) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin q → Fin (d + 1) =>
      ∑ s, (m s : ℕ) ≤ d),
    c r m * ∏ s, x s ^ (m s : ℕ)

/-- The coordinate derivative of `polyEval`. -/
def polyJac {q d : ℕ}
    (c : Fin q → (Fin q → Fin (d + 1)) → ℝ)
    (x : Fin q → ℝ) (r s : Fin q) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin q → Fin (d + 1) =>
      ∑ u, (m u : ℕ) ≤ d),
    c r m * (m s : ℕ) * x s ^ ((m s : ℕ) - 1) *
      ∏ u ∈ Finset.univ.filter (· ≠ s), x u ^ (m u : ℕ)

end AMPUniversality.StateEvol


