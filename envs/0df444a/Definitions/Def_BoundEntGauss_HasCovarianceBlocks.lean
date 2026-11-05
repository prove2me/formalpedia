-- Prove2me | Definitions.Def_BoundEntGauss_HasCovarianceBlocks
-- name    : BoundEntGauss_HasCovarianceBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:28.096352+00:00
-- url     : https://prove2.me/theorems/ceb2f956-fb87-4957-b47a-0676703a19e0
-- title:
--   A state with finite second moments, mean $d$ and covariance $\gamma$
-- statement:
--   Let $\rho$ be a density operator of $n\times m$ modes and $R=(R_\alpha)$ the canonical operators. The state $\rho$ **has finite second moments, mean $d$ and covariance $\gamma$** when all $R_\alpha^2$ have finite expectation in $\rho$, $d_\alpha=\operatorname{tr}(\rho R_\alpha)$, and $\gamma$ is the real symmetric matrix of Eq. (2),
--
--   $$
--   \gamma_{\alpha\beta} = 2\,\operatorname{Re}\operatorname{tr}\bigl[\rho\,(R_\alpha-d_\alpha)(R_\beta-d_\beta)\bigr],
--   $$
--
--   so that the vacuum has covariance $\mathbb 1$. Here $\gamma=\begin{pmatrix}A&C\\C^{T}&B\end{pmatrix}$ is assembled from Alice's block $A$, Bob's block $B$ and the cross block $C$, in canonical coordinates $(x_1,p_1,\dots\mid\dots)$ with Alice first.
--
--   This is the setting of Propositions 1 and 2 ("a state with finite second moments").
--
--   **Formalization Note** Finite second moments are expressed as finite mean photon number, and the mean and covariance through the first two derivatives at $t=0$ of $t\mapsto\operatorname{tr}\rho W(t\xi)$ for every direction $\xi$ (the published `HasBipartiteMoments`, in grouped coordinates, reached by a permutation). The moments fix only the symmetric part of $\gamma$, so symmetry of $\gamma$ is required explicitly.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, Eq. (2), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation HasBipartiteMoments)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks covarianceBlockMatrix bipartiteGroupedIndex)

namespace BoundEntGauss

/-- **A state with finite second moments, mean `d` and covariance `γ`.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, Eq. (2), p. 2.

`HasCovarianceBlocks ρ g d` says that the bipartite density `ρ` of `n × m` modes has finite
second moments, that its mean vector `m_α = tr(ρ R_α)` is `d`, and that its covariance matrix
(Eq. (2), doubled convention: vacuum covariance `I`, `ħ = 1`) is the real symmetric matrix
`γ = covarianceBlockMatrix g`, in the interleaved canonical coordinates
`(x₁, p₁, …, xₙ, pₙ | x_{n+1}, p_{n+1}, …)` (Alice's `QuadratureIndex n` first).

**Formalization Note.** Reading: "finite second moments with mean `d` and covariance `γ`" is the
published `Claimed50.P47.HasBipartiteMoments`: finite mean photon number (equivalent to finite
second moments for finitely many modes), and for every real direction `ξ` the first and second
derivatives at `t = 0` of the characteristic function `t ↦ tr ρ W(tξ)` are
`i ξᵀσd` and `−(½ ξᵀσᵀγσξ + (ξᵀσd)²)`, i.e. the mean and the second moment of the observable
`ξᵀσR`. P47 uses grouped coordinates (all `x`, then all `p`); the published permutation
`bipartiteGroupedIndex` relabels without rescaling. The moments fix only the symmetric part of
`γ`, so symmetry of `γ` is required, as the paper states after Eq. (2). -/
def HasCovarianceBlocks {n m : ℕ} (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
    (g : CovarianceBlocks n m) (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) : Prop :=
  (covarianceBlockMatrix g).transpose = covarianceBlockMatrix g ∧
    HasBipartiteMoments ρ.coefficients (d ∘ bipartiteGroupedIndex)
      ((covarianceBlockMatrix g).submatrix bipartiteGroupedIndex bipartiteGroupedIndex)

end BoundEntGauss


