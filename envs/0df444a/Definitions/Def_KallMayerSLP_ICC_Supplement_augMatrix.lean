-- Prove2me | Definitions.Def_KallMayerSLP_ICC_Supplement_augMatrix
-- name    : KallMayerSLP_ICC_Supplement_augMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:38:20.304363+00:00
-- url     : https://prove2.me/theorems/78be7f6a-babc-4775-b3e8-740055daa4e4
-- title:
--   The random matrix $(T(\xi),h(\xi))$ of all random entries
-- statement:
--   Let $\xi$ be a random element of a space $\Xi$, let $T(\xi)$ be a random $s\times n$ technology matrix and $h(\xi)\in\mathbb R^s$ a random right-hand side. Their augmented matrix is the random $s\times(n+1)$ matrix
--   $$
--   (T(\xi),h(\xi))=\big(\zeta^{(1)},\dots,\zeta^{(n)},\zeta^{(n+1)}\big)=\begin{pmatrix}\eta^{(1)\mathrm T}\\ \vdots\\ \eta^{(s)\mathrm T}\end{pmatrix},
--   $$
--   whose column $\zeta^{(j)}\in\mathbb R^s$ is the $j$-th column of $T(\xi)$ for $j\le n$ and $h(\xi)$ for $j=n+1$, and whose row $\eta^{(i)\mathrm T}=(T_{i1}(\xi),\dots,T_{in}(\xi),h_i(\xi))$ is the $i$-th row.
--
--   The column-wise and row-wise views of this matrix carry the two covariance hypotheses of Prékopa's theorem on joint normal probability constraints.
--
--   **Formalization Note** Indices are $0$-based: column `Fin.last n` is $h(\xi)$ and column `Fin.castSucc j` is the $j$-th column of $T(\xi)$. $T$ and $h$ are arbitrary functions of $\xi$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.6, p.137 (PDF 147)

import Mathlib

open Matrix

namespace KallMayerSLP.ICC.Supplement

/-- **The random matrix `(T(ξ), h(ξ))` of all random entries.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.6, p.137 (PDF 147):
`(T(ξ), h(ξ)) = (ζ^(1), …, ζ^(n), ζ^(n+1))`, whose `j`-th column `ζ^(j)` is the `j`-th column of
`T(ξ)` for `j ≤ n` and the right-hand side `h(ξ)` for `j = n + 1`; its `i`-th row is
`η^(i)ᵀ = (T_i1(ξ), …, T_in(ξ), h_i(ξ))`.

**Formalization Note.** Index base `0`: the columns are `Fin (n + 1)`, the book's column `n + 1`
(the right-hand side) is `Fin.last n`, and the column `j ≤ n` of `T(ξ)` is `Fin.castSucc j`.
`T` and `h` are arbitrary functions of `ξ`. -/
def augMatrix {Ξ : Type*} {s n : ℕ} (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (ξ : Ξ) : Matrix (Fin s) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (h ξ i) (fun j' => T ξ i j') j

end KallMayerSLP.ICC.Supplement


