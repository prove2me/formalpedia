-- Prove2me | Definitions.Def_GaussToomCook_vandMatrix
-- name    : GaussToomCook_vandMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:11.134504+00:00
-- url     : https://prove2.me/theorems/8cc48439-7fc2-4150-8ef7-f08474794d24
-- title:
--   The Vandermonde matrix $V(S)$ and its rows
-- statement:
--   For evaluation points $S=((x_j,y_j))_{0\le j\le 2k-2}$ the **Vandermonde matrix** of eq. (85) is the $(2k-1)\times(2k-1)$ matrix over $\mathbb Z[i]$
--   $$V(S)=\big[x^{c}\,y^{|S|-1-c}\big]_{(x,y)\in S,\ 0\le c\le |S|-1},\qquad |S|=2k-1 ,$$
--   whose row for the point $(x_j,y_j)$ is $(x_j^{c}\,y_j^{\,2k-2-c})_{c=0,\dots,2k-2}$. Multiplying it by the coefficient vector of the product polynomial $Q$ gives the values $Q(x,y)$, $(x,y)\in S$ (eq. (84)).
--
--   The module also defines the rows of $V(S)$ as vectors of the space $W=\bigoplus_{j=0}^{2k-2}\mathbb Q(i)\,q_j$ in which the interpolation phase works, written in the standard basis $q_0,\dots,q_{2k-2}$.
--
--   **Formalization Note** $V(S)$ is Mathlib's `Matrix.projVandermonde` of the two coordinates. $W$ is represented by $\mathbb C^{2k-1}$ (`Fin (2k − 1) → ℂ`) with $\mathbb Z[i]$ embedded by `GaussianInt.toComplex`; the paper's upper index $2k-1$ in $\bigoplus_{j=0}^{2k-1}$ is a typo for $2k-2$.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.1, eq. (85) and p. 30 (PDF p. 32)

import Mathlib

namespace GaussToomCook

/-- **The Vandermonde matrix `V(S)`**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, eq. (85), p. 30 (PDF 32):
`V(S) = [x^j y^{|S|−1−j}]_{(x,y)∈S, 0≤j≤|S|−1}`, a square matrix with entries in `ℤ[i]`. With
`|S| = 2k − 1` the entry in row `(x, y) = S r` and column `c` is `x^c · y^{2k−2−c}`.

**Formalization Note.** This is Mathlib's `Matrix.projVandermonde` applied to the first and second
coordinates of the points: its `(r, c)` entry is `(S r).1 ^ c * (S r).2 ^ (2k − 1 − 1 − c)`. -/
def vandMatrix (k : ℕ) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt) :
    Matrix (Fin (2 * k - 1)) (Fin (2 * k - 1)) GaussianInt :=
  Matrix.projVandermonde (fun j => (S j).1) (fun j => (S j).2)

/-- **The row vectors of `V(S)` as vectors of `W`**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, p. 30 (PDF 32):
the row of the point `S j`, `(x^c y^{2k−2−c})_{c = 0, …, 2k−2}`, viewed in the coordinates of the
standard basis `q_0, …, q_{2k−2}` of `W`.

**Formalization Note.** `W = ⊕ ℚ(i) q_j` is represented as `Fin (2k − 1) → ℂ`, with `ℤ[i]` embedded in `ℂ`
by `GaussianInt.toComplex`; every vector the interpolation phase can produce lies in `ℚ(i)^{2k−1}`. The
paper's upper index `2k − 1` in `⊕_{j=0}^{2k−1}` is a typo for `2k − 2` (the basis is `q_0, …, q_{2k−2}`). -/
noncomputable def vandRow (k : ℕ) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (j : Fin (2 * k - 1)) : Fin (2 * k - 1) → ℂ :=
  fun c => GaussianInt.toComplex (vandMatrix k S j c)

end GaussToomCook


