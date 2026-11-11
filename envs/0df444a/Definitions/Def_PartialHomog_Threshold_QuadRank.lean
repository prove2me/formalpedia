-- Prove2me | Definitions.Def_PartialHomog_Threshold_QuadRank
-- name    : PartialHomog_Threshold_QuadRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:26:36.629298+00:00
-- url     : https://prove2.me/theorems/d5a0f29e-45ad-49fb-882d-8bcb3bd78094
-- title:
--   The rank of a real quadratic form (rank of its Hessian / symmetric matrix)
-- statement:
--   For a real quadratic form $f(z)=z^{\mathsf T}Sz$ with $S$ symmetric, the **rank** of $f$ is the rank of $S$, equivalently of its Hessian matrix
--   $$\Big(\frac{\partial^2 f}{\partial z_a\,\partial z_b}\Big)_{a,b}=2S .$$
--   For example $z_0z_1+z_2z_3$ has rank $4$ and a product of two linear forms has rank at most $2$.
--
--   **Formalization Note** `quadRank f` is `Matrix.rank` of the real $N\times N$ matrix whose $(a,b)$ entry is the constant coefficient of the formal second derivative `pderiv a (pderiv b f)`; for a quadratic form that derivative is a constant.
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 26 (PDF 28), Lemma E.13; p. 27 (PDF 29), proof of Lemma E.13

import Mathlib

/-!
# The rank of a real quadratic form

Spiizer, *Partial Homogenization and the Structure of Optimal Algebraic Algorithms*,
STOC 2027 submission, §E.2, Lemma E.13 and its proof (pp. 26–27).

For a real quadratic form `f(z) = zᵀ S z` (`S` symmetric) in `z = (z_0, …, z_{N-1})`, the rank of
`f` is the rank of `S`, equivalently the rank of its Hessian matrix `(∂²f/∂z_a∂z_b)_{a,b} = 2S`.
-/

namespace PartialHomog.Threshold

open MvPolynomial

/-- The rank of a real quadratic form `f`: the rank of the `N × N` real matrix of second formal
partial derivatives `(∂²f / ∂z_a ∂z_b)` (constant terms taken, which is the whole derivative when
`f` is a quadratic form). -/
noncomputable def quadRank {N : ℕ} (f : MvPolynomial (Fin N) ℝ) : ℕ :=
  (Matrix.of fun a b : Fin N => constantCoeff (pderiv a (pderiv b f))).rank

end PartialHomog.Threshold


