-- Prove2me | Definitions.Def_SpencerEight_evenPoly
-- name    : SpencerEight_evenPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:37.929432+00:00
-- url     : https://prove2.me/theorems/85ee742b-8adf-4ddd-b77d-7259ee7d9053
-- title:
--   Even matrix polynomial $p(X)=\sum_{j\le d}a_jX^{2j}$
-- statement:
--   For coefficients $a_0,\dots,a_d$ and a square matrix $X$, put
--   $$p(X):=\sum_{j=0}^d a_jX^{2j},\qquad X^0=I.$$
--   On a symmetric $X$ this is the functional calculus of the scalar polynomial $p(u)=\sum_j a_ju^{2j}$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.44, p.105 (PDF p.105); Lemma 8.48, p.108 (PDF p.108)

import Mathlib

namespace SpencerEight

/-- The even matrix polynomial `p(X) := ∑_{j=0}^d a_j X^{2j}` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.44, p.105 (PDF p.105), Lemma 8.48, p.108 (PDF p.108)).

**Formalization Note** The polynomial evaluated directly at the matrix `X`, with `X⁰ = I`; for symmetric `X` this equals the functional calculus `p(X)`. -/
def evenPoly {d : Type*} [Fintype d] [DecidableEq d] (a : ℕ → ℝ) (deg : ℕ) (X : Matrix d d ℝ) :
    Matrix d d ℝ :=
  ∑ j ∈ Finset.range (deg + 1), a j • X ^ (2 * j)

end SpencerEight


