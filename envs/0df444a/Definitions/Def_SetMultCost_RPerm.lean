-- Prove2me | Definitions.Def_SetMultCost_RPerm
-- name    : SetMultCost_RPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:01.308634+00:00
-- url     : https://prove2.me/theorems/68299e6a-c43c-4808-be93-862bb86e56d8
-- title:
--   Rectangular permanent and the Binet–Minc terms
-- statement:
--   For $d\le n$ and a $d\times n$ matrix $X$, the **rectangular permanent** is
--
--   $$\mathrm{RPerm}_{d,n}(X)=\sum_{S\subseteq[n],\,|S|=d}\mathrm{Perm}\big(X|_{[d]\times S}\big).$$
--
--   For a set partition $\lambda$ of $[d]$, the **Binet–Minc term** is
--
--   $$(-1)^{d-|\lambda|}\prod_{S\in\lambda}(|S|-1)!\sum_{j=1}^n\prod_{i\in S}x_{i,j}.$$
--
--   The rectangular permanent is the gadget extracting set-multilinear components, and the terms are the summands of its depth-four expression.
--
--   **Formalization Note** $X$ has entries in any commutative ring, so the symbolic matrix is an instance. $X|_{[d]\times S}$ lists the columns of $S$ in increasing order. Parts of a `Finpartition` are nonempty, so $|S|-1$ is exact.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Definition 1.4 and (1.6), p.5

import Mathlib

namespace SetMultCost

/-- **Rectangular permanent.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 1.4, p.5: "RPermd,n(X) := ∑_{S⊆[n], |S|=d}
Perm(X|[d]×S)".

**Formalization Note.** `X` has entries in any commutative ring, so the symbolic matrix is the
instance over `MvPolynomial`. `X|[d]×S` lists the columns of `S` in increasing order. -/
noncomputable def RPerm {R : Type*} [CommRing R] {d n : ℕ} (X : Matrix (Fin d) (Fin n) R) : R :=
  ∑ S : {S : Finset (Fin n) // S.card = d},
    Matrix.permanent (X.submatrix id (S.1.orderEmbOfFin S.2))

/-- The term of `λ ∈ P(d)` in the Binet–Minc identity (1.6), p.5:
`(−1)^{d − |λ|} ∏_{S ∈ λ} (|S| − 1)! ∑_{j=1}^n ∏_{i ∈ S} x_{i,j}`. Parts of a `Finpartition` are
nonempty, so `|S| − 1` is exact, and `|λ| ≤ d`. -/
noncomputable def binetMincTerm {R : Type*} [CommRing R] {d n : ℕ} (X : Matrix (Fin d) (Fin n) R)
    (lam : Finpartition (Finset.univ : Finset (Fin d))) : R :=
  (-1) ^ (d - lam.parts.card) *
    ∏ S ∈ lam.parts, (((S.card - 1).factorial : R) * ∑ j, ∏ i ∈ S, X i j)

end SetMultCost


