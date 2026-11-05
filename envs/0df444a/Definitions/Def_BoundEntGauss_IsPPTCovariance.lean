-- Prove2me | Definitions.Def_BoundEntGauss_IsPPTCovariance
-- name    : BoundEntGauss_IsPPTCovariance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:37.474942+00:00
-- url     : https://prove2.me/theorems/5af0e780-59ce-4773-9fa5-0df1db6c6fb8
-- title:
--   ppt-covariance (Definition 1)
-- statement:
--   A real symmetric $2(n+m)\times2(n+m)$ matrix $\gamma$ is a **ppt-covariance** if
--
--   $$
--   \gamma+i\sigma\ge0\qquad\text{and}\qquad\gamma+i\tilde\sigma\ge0 ,
--   $$
--
--   where $\ge0$ means positive semidefinite as a complex Hermitian matrix, $\sigma=\sigma_A\oplus\sigma_B$ and $\tilde\sigma=(-\sigma_A)\oplus\sigma_B$.
--
--   The first condition says that $\gamma$ is the covariance matrix of a quantum state; the second says that the partially transposed state is again a state (Proposition 2).
--
--   **Formalization Note** The sign $+i$ is as printed; for real symmetric $\gamma$ it is equivalent to $\gamma-i\sigma\ge0$ by complex conjugation.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Definition 1, p. 3

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_sigmaTilde

open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks covarianceBlockMatrix)

namespace BoundEntGauss

/-- **ppt-covariance.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Definition 1, p. 3.

A real symmetric matrix `γ` (here `γ = covarianceBlockMatrix g`, an `n × m`-mode bipartite
covariance in interleaved coordinates) is a *ppt-covariance* if `γ + iσ ≥ 0` and `γ + iσ̃ ≥ 0`,
where `σ = σ_A ⊕ σ_B` and `σ̃ = (−σ_A) ⊕ σ_B`, and `≥ 0` is positive semidefiniteness of the
complex Hermitian matrix.

**Formalization Note.** The `+iσ` is as printed in Definition 1; for a real symmetric `γ`,
`γ + iσ ≥ 0` is equivalent to `γ − iσ ≥ 0` (complex conjugation), which is the convention of the
published `IsPhysicalCovariance`. Symmetry is an explicit conjunct. -/
def IsPPTCovariance {n m : ℕ} (g : CovarianceBlocks n m) : Prop :=
  (covarianceBlockMatrix g).transpose = covarianceBlockMatrix g ∧
    (complexify (covarianceBlockMatrix g) + Complex.I • complexify (totalSigma n m)).PosSemidef ∧
    (complexify (covarianceBlockMatrix g) + Complex.I • complexify (sigmaTilde n m)).PosSemidef

end BoundEntGauss


