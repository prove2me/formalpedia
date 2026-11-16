-- Prove2me | Definitions.Def_ROLDescent_Supplement_condCov
-- name    : ROLDescent_Supplement_condCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:54:17.654193+00:00
-- url     : https://prove2.me/theorems/26a169b4-8603-4cd2-860c-85978a026450
-- title:
--   Conditional covariance matrix $\Sigma^{\mu_{S,s}}$ of the remaining spins
-- statement:
--   For a law $\mu$ on $\{0,1\}^V$, a set $S\subseteq V$ and an assignment $s\in\{0,1\}^S$, the **conditional covariance matrix** of the remaining spins is the matrix indexed by $i,j\in V\setminus S$ with entries
--
--   $$\Sigma^{\mu_{S,s}}_{ij}=\operatorname{Cov}_{\mu_{S,s}}(X_i,X_j)=\mathbb E_{\mu_{S,s}}\big[(X_i-\mathbb E_{\mu_{S,s}}X_i)(X_j-\mathbb E_{\mu_{S,s}}X_j)\big].$$
--
--   Its diagonal entries are the conditional variances $\operatorname{Var}_{\mu_{S,s}}(X_i)$, the entries of the diagonal matrix $D^{\mu_{S,s}}$.
--
--   **Formalization Note** The expectation is the finite sum against the conditional law $\mu_{S,s}$; the variance $D^{\mu_{S,s}}_{ii}$ is read off as the diagonal entry of this matrix.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, p.50 (PDF 50)

import Mathlib
import Definitions.Def_ROLDescent_Supplement_condLaw

namespace ROLDescent.Supplement

/-- **Conditional covariance matrix** `Σ^{µ_{S,s}}` of the remaining spins.
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, p.50 (PDF 50): "Define Σ^{µS,s}_{ij} = Cov_{µS,s}(X_i, X_j),
D^{µS,s} = diag(Var_{µS,s}(X_i)). Here covariance and variance are taken under the conditional law
µS,s: Cov_{µS,s}(X_i, X_j) = E_{µS,s}[(X_i − E_{µS,s}X_i)(X_j − E_{µS,s}X_j)],
Var_{µS,s}(X_i) = Cov_{µS,s}(X_i, X_i). Thus Σ^{µS,s} is the covariance matrix of the remaining
spins".

**Formalization Note** The matrix is indexed by the remaining sites `{i : V // i ∉ S}`; the spin
`X_i` is `1` on `x i = true` and `0` otherwise, and `E_{µS,s}` is the finite sum against
`condLaw μ S s`. The variance `Var_{µS,s}(X_i)` (the diagonal of `D^{µS,s}`) is the diagonal entry
`condCov μ S s i i`. -/
noncomputable def condCov {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (S : Finset V)
    (s : S → Bool) : Matrix {i : V // i ∉ S} {i : V // i ∉ S} ℝ :=
  fun i j =>
    ∑ x, condLaw μ S s x *
      (((if x i.1 then 1 else 0) - ∑ y, condLaw μ S s y * (if y i.1 then 1 else 0)) *
        ((if x j.1 then 1 else 0) - ∑ y, condLaw μ S s y * (if y j.1 then 1 else 0)))

end ROLDescent.Supplement


