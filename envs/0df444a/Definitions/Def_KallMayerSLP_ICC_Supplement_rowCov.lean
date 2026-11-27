-- Prove2me | Definitions.Def_KallMayerSLP_ICC_Supplement_rowCov
-- name    : KallMayerSLP_ICC_Supplement_rowCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:39:25.522853+00:00
-- url     : https://prove2.me/theorems/d2be2e0d-1f27-5718-9919-d17e7a477451
-- title:
--   Row covariance blocks $\bar C^{(i,j)}$
-- statement:
--   For rows $i,j\in\{1,\dots,s\}$ of the augmented matrix $(T(\xi),h(\xi))$, with $\eta^{(i)\mathrm T}=(T_{i1}(\xi),\dots,T_{in}(\xi),h_i(\xi))$, $\bar C^{(i,j)}$ is the $(n+1)\times(n+1)$ covariance matrix of $\eta^{(i)}$ if $i=j$, and otherwise the cross-covariance matrix of $\eta^{(i)}$ and $\eta^{(j)}$:
--   $$
--   \bar C^{(i,j)}_{kl}=\operatorname{Cov}\big(\eta^{(i)}_k,\eta^{(j)}_l\big),\qquad k,l=1,\dots,n+1.
--   $$
--   The second hypothesis of Prékopa's theorem asks all these blocks to be multiples $\bar S_{ij}\bar C$ of one positive semidefinite matrix $\bar C$.
--
--   **Formalization Note** The covariance is Mathlib's `ProbabilityTheory.covariance` under the law $P$ of $\xi$; it agrees with the book's covariance for square-integrable entries. Indices are $0$-based.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.6, p.138 (PDF 148)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_Supplement_augMatrix

open Matrix MeasureTheory ProbabilityTheory

namespace KallMayerSLP.ICC.Supplement

/-- **The row covariance blocks `C̄^(i,j)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.6, p.138 (PDF 148):
"`C̄^(i,j)` is the `((n + 1) × (n + 1))` covariance matrix of `η^(i)` if `i = j`, otherwise the
cross-covariance matrix of `η^(i)` and `η^(j)`, `i = 1, …, s`, `j = 1, …, s`", where
`η^(i)ᵀ = (T_i1(ξ), …, T_in(ξ), h_i(ξ))` is the `i`-th row of `(T(ξ), h(ξ))`. Entry `(k, l)` is
`Cov(η^(i)_k, η^(j)_l)`.

**Formalization Note.** `P` is the law of `ξ` on `Ξ`; the covariance is Mathlib's
`ProbabilityTheory.covariance`, the book's covariance for square-integrable entries (as under the
joint normality of Theorem 2.12). Index base `0`; entry `Fin.last n` of a row is `h_i(ξ)`. -/
noncomputable def rowCov {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) {s n : ℕ}
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ) (i j : Fin s) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k l => covariance (fun ξ => augMatrix T h ξ i k) (fun ξ => augMatrix T h ξ j l) P

end KallMayerSLP.ICC.Supplement


