-- Prove2me | Definitions.Def_ROLDescent_Supplement_normCov
-- name    : ROLDescent_Supplement_normCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:54:47.387201+00:00
-- url     : https://prove2.me/theorems/f22e0435-e5b3-45db-bae0-5997468cb7fb
-- title:
--   Normalized covariance matrix $\hat\Sigma^{\mu_{S,s}}=D^{-1/2}\Sigma D^{-1/2}$, eq. (113)
-- statement:
--   With $\Sigma^{\mu_{S,s}}$ the conditional covariance matrix of the spins outside $S$ and $D^{\mu_{S,s}}=\operatorname{diag}(\operatorname{Var}_{\mu_{S,s}}(X_i))$, the **normalized covariance matrix** is
--
--   $$\hat\Sigma^{\mu_{S,s}}=(D^{\mu_{S,s}})^{-1/2}\,\Sigma^{\mu_{S,s}}\,(D^{\mu_{S,s}})^{-1/2},$$
--
--   the conditional correlation matrix of the remaining spins.
--
--   **Formalization Note** $(D^{\mu_{S,s}})^{-1/2}$ is the diagonal matrix with entries $1/\sqrt{\operatorname{Var}_{\mu_{S,s}}(X_i)}$; under full support the variances are positive.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eq. (113), p.50 (PDF 50)

import Mathlib
import Definitions.Def_ROLDescent_Supplement_condCov

namespace ROLDescent.Supplement

/-- **Normalized covariance matrix** `Σ̂^{µ_{S,s}}`, eq. (113).
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eq. (113), p.50 (PDF 50): "For the conditional law µS,s, define the normalized
covariance matrix Σ̂^{µS,s} := (D^{µS,s})^{−1/2} Σ^{µS,s} (D^{µS,s})^{−1/2}."

**Formalization Note** `D^{−1/2}` is the diagonal matrix with entries `(√Var_{µS,s}(X_i))⁻¹`,
`Var_{µS,s}(X_i) = condCov μ S s i i`; under full support these variances are positive (p.50), so
this is the paper's inverse square root. -/
noncomputable def normCov {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (S : Finset V)
    (s : S → Bool) : Matrix {i : V // i ∉ S} {i : V // i ∉ S} ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (condCov μ S s i i))⁻¹) * condCov μ S s *
    Matrix.diagonal (fun i => (Real.sqrt (condCov μ S s i i))⁻¹)

end ROLDescent.Supplement


