-- Prove2me | Definitions.Def_TwoWayCVQKD_crossCov
-- name    : TwoWayCVQKD_crossCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:40.964232+00:00
-- url     : https://prove2.me/theorems/5d01abe7-311d-4d66-acd1-6e970ca78315
-- title:
--   Covariances of linear combinations of Gaussian source variables
-- statement:
--   Let $\Sigma$ be the covariance matrix of a finite family of centered source variables, and let $x_i=\sum_s x_{is}\,s$ and $y_j=\sum_s y_{js}\,s$ be linear combinations of them. Their covariance is $\langle x_i y_j\rangle=x_i^{\mathsf T}\Sigma\,y_j$, and the matrix of these numbers is the output of this definition. With $x=y$ it is the covariance matrix of the family $x$.
--
--   All the output modes and decoded variables of the paper's protocols are linear combinations of independent Gaussian sources (vacua, EPR pairs, classical modulations), so the displayed covariance matrices of the paper are computed by this one formula.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.6 (correlation matrix) and pp.7–8 (output variables)

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.6 (the correlation matrix)
and pp.7–8 (output variables of the protocols): the covariances between two families of linear
combinations of source variables whose covariance matrix is `Sg`.

**Formalization Note** A variable is its coefficient vector `S → ℝ` over the source variables, so
`crossCov Sg x y i j = xᵢᵀ Sg yⱼ`. Every output of the paper's protocols is such a linear
combination of independent Gaussian sources, and `crossCov Sg x x` is the covariance matrix of the
family `x`. First moments play no role in any quantity of the paper. -/
def crossCov {S ι κ : Type*} [Fintype S] (Sg : Matrix S S ℝ) (x : ι → S → ℝ) (y : κ → S → ℝ) :
    Matrix ι κ ℝ :=
  fun i j => x i ⬝ᵥ (Sg.mulVec (y j))

end TwoWayCVQKD


