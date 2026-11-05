-- Prove2me | Definitions.Def_TwoWayCVQKD_condCov
-- name    : TwoWayCVQKD_condCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:35.204858+00:00
-- url     : https://prove2.me/theorems/0a14b630-2bdf-447c-91e7-a6a6783e3c6b
-- title:
--   Conditional covariance matrix (Schur complement)
-- statement:
--   For jointly Gaussian families $x$ and $y$ with $y$ classical, the covariance matrix of $x$ conditioned on $y$ is
--   $$
--   \mathbf V_{x|y}=\mathbf V_x-\mathbf C\,\mathbf V_y^{-1}\mathbf C^{\mathsf T},\qquad \mathbf C=\operatorname{cov}(x,y).
--   $$
--   This is the covariance of the residual variables $x-\hat x^{(y)}$ of the optimal linear estimator $\hat x^{(y)}$ of $x$ from $y$, the construction of Eqs. (37)–(39) of the paper. It gives Bob's and Eve's conditional matrices (21) and (53), and the matrix $\mathbf V_{E|X_B}$ of Eq. (35).
--
--   **Formalization Note** The paper minimizes the entropy over linear estimators. The Schur complement is the least residual covariance in the Loewner order, and the entropy is monotone in that order, so it is the minimizer. The inverse is Lean's matrix inverse, which returns $0$ on a singular matrix; each conditioning variable used by a rate has a positive definite covariance matrix for $0<T<1$, $W\ge1$, $V>1$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (21), (37)–(39), (53), pp.7–9

import Mathlib
import Definitions.Def_TwoWayCVQKD_crossCov

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (21), (37)–(39), (53),
pp.7–9: the covariance matrix of the family `x` conditioned on the classical Gaussian variables
`y`, namely the residual covariance `V_x - C V_y⁻¹ Cᵀ`, `C = cov(x, y)`, of the optimal linear
estimator of `x` from `y`.

**Formalization Note** This Schur complement is the Loewner-minimal residual of all linear
estimators of Eq. (37), so it attains the minimal entropy `H(E|X_B)` the paper asks for, and for
`y = X_A` it gives the conditional matrices of (21) and (53). `⁻¹` is the matrix inverse, and is
`0` on a singular matrix; for `T ∈ (0, 1)`, `W ≥ 1`, `V > 1` the matrix `V_y` is positive definite
in every use by a rate of this mission. -/
noncomputable def condCov {S ι κ : Type*} [Fintype S] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Sg : Matrix S S ℝ) (x : ι → S → ℝ) (y : κ → S → ℝ) : Matrix ι ι ℝ :=
  crossCov Sg x x - crossCov Sg x y * (crossCov Sg y y)⁻¹ * crossCov Sg y x

end TwoWayCVQKD


