-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily
-- name    : DetSupportRank_DeterminantSupport_DeterminantFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:57.977342+00:00
-- url     : https://prove2.me/theorems/03c6478b-2747-4334-8fbe-bb444afe7240
-- title:
--   Polynomials with determinant support
-- statement:
--   For an arbitrary field $F$ and a nonnegative integer $n$, choose an independent unit $c_\sigma\in F^\times$ for every permutation $\sigma\in S_n$. Define
--   $$D_c=\sum_{\sigma\in S_n}c_\sigma\prod_{i=1}^n x_{i,\sigma(i)}.$$
--   This is a formal polynomial, including over finite fields. For the target $n>2$; the formula itself also makes sense for $n=0$.
--
--   The construction parametrizes precisely the full determinant-support family; it imposes no symmetry or sign rule on the coefficients.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §1, the family Dₙ,F, p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- The family on p.2, with independent unit coefficients; formal polynomial equality. -/
def determinantSupportPolynomial {K : Type*} [Field K] {n : ℕ}
    (c : Equiv.Perm (Fin n) → Kˣ) : MvPolynomial (Fin n × Fin n) K :=
  ∑ σ, MvPolynomial.C (c σ : K) * ∏ i, MvPolynomial.X (i, σ i)

end DetSupportRank.DeterminantSupport


