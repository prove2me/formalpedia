-- Prove2me | Definitions.Def_ROLDescent_Supplement_influence
-- name    : ROLDescent_Supplement_influence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:55:23.934088+00:00
-- url     : https://prove2.me/theorems/e2c0307c-b9c4-418d-a132-08057b196438
-- title:
--   Signed influence matrix $\Psi^{\mu_{S,s}}$, eq. (112)
-- statement:
--   For a law $\mu$ on $\{0,1\}^V$, $S\subseteq V$ and $s\in\{0,1\}^S$, the **signed influence matrix** is indexed by the remaining sites $i,j\in V\setminus S$ and given by
--
--   $$\Psi^{\mu_{S,s}}_{ij}=\Pr_{\mu_{S,s}}[X_j=1\mid X_i=1]-\Pr_{\mu_{S,s}}[X_j=1\mid X_i=0]\quad(i\ne j),\qquad \Psi^{\mu_{S,s}}_{ii}=0 .$$
--
--   It measures how much fixing the spin at $i$ shifts the conditional probability that the spin at $j$ is $1$; its largest eigenvalue is the spectral-independence parameter.
--
--   **Formalization Note** The conditional probabilities are ratios $\mu_{S,s}(X_i=a,X_j=1)/\mu_{S,s}(X_i=a)$ of finite sums. The matrix is defined by these differences, not by the ratio $\Sigma_{ij}/D_{ii}$, and its diagonal is $0$ (the paper's convention).
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, eq. (112), p.50 (PDF 50)

import Mathlib
import Definitions.Def_ROLDescent_Supplement_condLaw

namespace ROLDescent.Supplement

/-- **Signed influence matrix** `Ψ^{µ_{S,s}}`, eq. (112).
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, eq. (112), p.50 (PDF 50): "Fix the signed influence convention
Ψ^{µS,s}_{ij} = Pr_{µS,s}[X_j = 1 | X_i = 1] − Pr_{µS,s}[X_j = 1 | X_i = 0] (i ≠ j), Ψ^{µS,s}_{ii} = 0."

**Formalization Note** Defined by the conditional-probability difference, not by the ratio
`Σ_{ij}/D_{ii}` (that equality is proved in the paper). Indexed by the remaining sites
`{i : V // i ∉ S}`; `Pr_{µS,s}[X_j = 1 | X_i = a]` is `µS,s(X_i = a, X_j = 1) / µS,s(X_i = a)` with
real division. Under full support both denominators are positive for `i ∉ S`. The diagonal is
`0` (the paper's convention; it differs from conventions with ones on the diagonal). -/
noncomputable def influence {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (S : Finset V)
    (s : S → Bool) : Matrix {i : V // i ∉ S} {i : V // i ∉ S} ℝ :=
  fun i j =>
    if i = j then 0 else
      (∑ x, condLaw μ S s x * (if x i.1 = true ∧ x j.1 = true then 1 else 0)) /
          (∑ x, condLaw μ S s x * (if x i.1 = true then 1 else 0)) -
        (∑ x, condLaw μ S s x * (if x i.1 = false ∧ x j.1 = true then 1 else 0)) /
          (∑ x, condLaw μ S s x * (if x i.1 = false then 1 else 0))

end ROLDescent.Supplement


