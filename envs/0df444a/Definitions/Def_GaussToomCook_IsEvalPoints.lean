-- Prove2me | Definitions.Def_GaussToomCook_IsEvalPoints
-- name    : GaussToomCook_IsEvalPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:07.71896+00:00
-- url     : https://prove2.me/theorems/37393d54-19a4-4756-8240-3158ff6bd393
-- title:
--   Evaluation points of Gaussian Toom–Cook-$k$
-- statement:
--   Let $k$ be a positive integer. A family $S=(S_0,\dots,S_{2k-2})$ of pairs $S_j=(x_j,y_j)\in\mathbb Z[i]^2$ is a set of **evaluation points** for Gaussian Toom–Cook-$k$ if
--
--   1. every pair is nonzero, $(x_j,y_j)\neq(0,0)$;
--   2. no two of them are proportional: for $j\neq j'$,
--   $$x_j\,y_{j'}-x_{j'}\,y_j\neq 0 .$$
--
--   Equivalently, the $2k-1$ pairs project onto $2k-1$ distinct points of the projective line $\mathbb P^1(\mathbb Q(i))$; a pair $(x,y)$ with $y\ne0$ stands for the affine point $x/y$ and $(x,0)$ for the point $\infty$. These are the points at which Gaussian Toom–Cook-$k$ evaluates its two polynomials.
--
--   **Formalization Note** The family is indexed by `Fin (2k − 1)`. Nonvanishing cross products for distinct indices make the indexing injective, so the family is a set of exactly $2k-1$ points.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §6, p. 13 (PDF p. 15)

import Mathlib

namespace GaussToomCook

/-- **Evaluation points of Gaussian Toom–Cook-k**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §6, p. 13 (PDF 15):
`S ⊂ ℤ[i]² \ {(0,0)}` is a set of `2k − 1` pairs of Gaussian integers that project onto `2k − 1` distinct
points of the projective line `P¹(ℚ(i))`, i.e. no two are scalar multiples of each other over `ℚ(i)^×`.

**Formalization Note.** The set is indexed by `Fin (2k − 1)` (natural-number subtraction; the paper has
`k ∈ ℤ_{>0}`). For nonzero pairs `(x, y)`, `(u, v)`, "not proportional over `ℚ(i)^×`" is equivalent to
`x v − u y ≠ 0`; requiring this for distinct indices also makes the indexing injective, so the image is a
set of exactly `2k − 1` points. -/
def IsEvalPoints (k : ℕ) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt) : Prop :=
  (∀ j, S j ≠ (0, 0)) ∧
    ∀ j j', j ≠ j' → (S j).1 * (S j').2 - (S j').1 * (S j).2 ≠ 0

end GaussToomCook


