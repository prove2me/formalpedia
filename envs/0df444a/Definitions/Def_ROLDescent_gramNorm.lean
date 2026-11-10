-- Prove2me | Definitions.Def_ROLDescent_gramNorm
-- name    : ROLDescent_gramNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:23.659595+00:00
-- url     : https://prove2.me/theorems/7b258396-3e52-4011-a274-e2319ac6f6eb
-- title:
--   Gram norm $\theta_\tau$
-- statement:
--   Let $\Pi_\tau$ be the orthogonal projection of $\mathcal K$ onto $\mathcal I_\tau$, and $E_{\tau,i} = \Pi_\tau - \Pi_{\tau i}$ the projection removed by the step $\tau \to \tau i$. The **Gram norm** of the face $\tau$ is
--
--   $$\theta_\tau = \Big\| \sum_{i \in N_\tau} \pi_\tau(i)\, E_{\tau,i}\big|_{\mathcal I_\tau} \Big\| .$$
--
--   It measures the worst-case average loss of squared norm under one localization step: $\sum_i \pi_\tau(i)\|E_{\tau,i} b\|^2 \le \theta_\tau \|b\|^2$ for $b \in \mathcal I_\tau$.
--
--   **Formalization Note** The restriction to $\mathcal I_\tau$ is composition with the isometric inclusion $\mathcal I_\tau \hookrightarrow \mathcal K$, so this is the operator norm of a map $\mathcal I_\tau \to \mathcal K$; under the nesting $\mathcal I_{\tau i} \subseteq \mathcal I_\tau$ its range lies in $\mathcal I_\tau$, so it is the paper's norm.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.2.1, eq. (75), p.31 (PDF 31)

import Mathlib
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb

namespace ROLDescent

/-- **Gram norm** `θ_τ`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.2.1, eq. (75), p.31 (PDF 31): "For each
internal node τ, define its Gram norm by θ_τ := ‖Σ_{i∈N_τ} π_τ(i) E_τ,i|_{I_τ}‖", where (74)
"Let Π_τ be the orthogonal projection in K onto I_τ. … E_τ,i = Π_τ − Π_τi".

**Formalization Note** `Π_τ` is `(I τ).starProjection : K →L[ℂ] K`. The operator
`Σ π_τ(i) E_τ,i` is restricted to `I_τ` by composing with the isometric inclusion
`(I τ).subtypeL`, so the norm is that of a map `I_τ → K`. Under the nesting `I_τi ⊆ I_τ` its range
lies in `I_τ`, so this is the paper's norm on `I_τ`. -/
noncomputable def gramNorm {V : Type*} [Fintype V] [DecidableEq V] {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (I : Finset V → Submodule ℂ K)
    (τ : Finset V) : ℝ :=
  ‖(∑ i ∈ HDXConc.linkVerts X τ, ((outProb X d w τ i : ℝ) : ℂ) •
      ((I τ).starProjection - (I (insert i τ)).starProjection)) ∘L (I τ).subtypeL‖

end ROLDescent


