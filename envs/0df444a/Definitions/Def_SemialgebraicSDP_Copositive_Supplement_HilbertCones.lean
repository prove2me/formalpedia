-- Prove2me | Definitions.Def_SemialgebraicSDP_Copositive_Supplement_HilbertCones
-- name    : SemialgebraicSDP_Copositive_Supplement_HilbertCones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:43:11.479827+00:00
-- url     : https://prove2.me/theorems/87527a3e-693d-43fe-93a2-c8a55b320f3f
-- title:
--   §3.2 — nonnegative forms and sums of squares of homogeneous forms
-- statement:
--   Let $P_{n,m}$ consist of homogeneous real polynomials of degree $m$ that are nonnegative everywhere. For even degree $m=2d$, let $\Sigma_{n,2d}$ consist of finite sums of squares of homogeneous degree-$d$ forms:
--   $$\Sigma_{n,2d}=\left\{\sum_{i=1}^k h_i^2: h_i\text{ homogeneous of degree }d,\ k\in\mathbb N\right\}.$$
--   These are the two cones compared in Hilbert's Theorem 3.2. Forms are Mathlib multivariate polynomials on `Fin n`; zero is homogeneous in each degree and the empty sum is allowed. No norm, closure or limiting sum is involved. `sosForms n d` indexes the half degree, while `nonnegativeForms n m` indexes the full degree.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, pp. 295, 297, Definition 2.3 and §3.2

import Mathlib

namespace SemialgebraicSDP.Copositive.Supplement

/-- Pₙ,ₘ, the nonnegative homogeneous forms of degree m (§3.2, p. 297). -/
def nonnegativeForms (n m : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | p.IsHomogeneous m ∧ ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x p}

/-- Σₙ,₂d: finite sums of squares of forms of degree d (zero included). -/
def sosForms (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | ∃ k : ℕ, ∃ h : Fin k → MvPolynomial (Fin n) ℝ,
    (∀ i, (h i).IsHomogeneous d) ∧ p = ∑ i, h i ^ 2}

end SemialgebraicSDP.Copositive.Supplement


