-- Prove2me | Definitions.Def_KallMayerSLP_ICC_Supplement_colCov
-- name    : KallMayerSLP_ICC_Supplement_colCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:39:04.259973+00:00
-- url     : https://prove2.me/theorems/6b3cb072-155e-5206-a9a6-f63d387a098e
-- title:
--   Column covariance blocks $C^{(i,j)}$
-- statement:
--   For columns $i,j\in\{1,\dots,n+1\}$ of the augmented matrix $(T(\xi),h(\xi))$, $C^{(i,j)}$ is the $s\times s$ covariance matrix of $\zeta^{(i)}$ if $i=j$, and otherwise the cross-covariance matrix of $\zeta^{(i)}$ and $\zeta^{(j)}$:
--   $$
--   C^{(i,j)}_{kl}=\operatorname{Cov}\big(\zeta^{(i)}_k,\zeta^{(j)}_l\big)=\mathbb E\Big[\big(\zeta^{(i)}_k-\mathbb E\zeta^{(i)}_k\big)\big(\zeta^{(j)}_l-\mathbb E\zeta^{(j)}_l\big)\Big],\qquad k,l=1,\dots,s.
--   $$
--   The first hypothesis of Prékopa's theorem asks all these blocks to be multiples $S_{ij}C$ of one positive semidefinite matrix $C$.
--
--   **Formalization Note** The covariance is Mathlib's `ProbabilityTheory.covariance` under the law $P$ of $\xi$, a Bochner integral; it agrees with the book's covariance for square-integrable entries, which holds under joint normality. Indices are $0$-based.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.6, p.137 (PDF 147)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_Supplement_augMatrix

open Matrix MeasureTheory ProbabilityTheory

namespace KallMayerSLP.ICC.Supplement

/-- **The column covariance blocks `C^(i,j)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.6, p.137 (PDF 147):
"`C^(i,j)` is the `(s × s)` covariance matrix of `ζ^(i)` if `i = j`, otherwise the
cross-covariance matrix of `ζ^(i)` and `ζ^(j)`, `i = 1, …, n + 1`, `j = 1, …, n + 1`", where
`ζ^(j)` is the `j`-th column of `(T(ξ), h(ξ))`. Entry `(k, l)` is
`Cov(ζ^(i)_k, ζ^(j)_l) = 𝔼[(ζ^(i)_k − 𝔼ζ^(i)_k)(ζ^(j)_l − 𝔼ζ^(j)_l)]`.

**Formalization Note.** `P` is the law of `ξ` on `Ξ`, and the covariance is Mathlib's
`ProbabilityTheory.covariance` (a Bochner integral). It is the book's covariance whenever the
entries are square integrable, which holds under the joint normality assumed in Theorem 2.12.
Index base `0`; column `Fin.last n` is `h(ξ)`. -/
noncomputable def colCov {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) {s n : ℕ}
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ) (i j : Fin (n + 1)) :
    Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun k l => covariance (fun ξ => augMatrix T h ξ k i) (fun ξ => augMatrix T h ξ l j) P

end KallMayerSLP.ICC.Supplement


