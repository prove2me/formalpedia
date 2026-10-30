-- Prove2me | Definitions.Def_FoundationsRL_DECLower_kernelHull
-- name    : FoundationsRL_DECLower_kernelHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:08:54.006446+00:00
-- url     : https://prove2.me/theorems/154db0eb-09b2-4eb7-bfed-3c834380b161
-- title:
--   Convex hull $\mathrm{co}(\mathcal M)$ of a model class
-- statement:
--   For a class $\mathcal M$ of kernels $\Pi\to\Delta(\mathbb R\times\mathcal O)$, the **convex hull** $\mathrm{co}(\mathcal M)$ is the set of finite mixtures
--
--   $$
--   \widehat M(\pi)=\sum_{i=1}^n\lambda_i M_i(\pi),\qquad M_i\in\mathcal M,\ \lambda_i\ge 0,\ \sum_{i=1}^n\lambda_i=1,
--   $$
--
--   the mixture taken decision by decision.
--
--   The constrained Decision-Estimation Coefficient takes its supremum over reference models $\widehat M\in\mathrm{co}(\mathcal M)$. A mixture of models is a model.
--
--   **Formalization Note** The notes do not define $\mathrm{co}(\mathcal M)$ further; it is read as the convex hull, the set of finite convex combinations.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.3, p. 97 and §6.5.1, p. 104 (co(M))

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Convex hull of a model class** `co(M)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.3, p. 97 and §6.5.1, p. 104 (`sup_{M̂ ∈ co(M)}`).

`kernelHull Ms` is the set of finite mixtures `M̂(π) = Σ_i λ_i M_i(π)` with `M_i ∈ Ms`,
`λ_i ≥ 0`, `Σ_i λ_i = 1`, the mixture taken decision by decision.

**Formalization Note.** The notes do not define `co(M)` further; it is read as the convex hull,
i.e. the set of finite convex combinations of members of `M` (pointwise in the decision).
A mixture of models is a model. -/
def kernelHull {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (Ms : Set (Kernel D (ℝ × O))) : Set (Kernel D (ℝ × O)) :=
  {K | ∃ (n : ℕ) (w : Fin n → ℝ) (Mi : Fin n → Kernel D (ℝ × O)),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, Mi i ∈ Ms) ∧
      ∀ d, K d = ∑ i, ENNReal.ofReal (w i) • Mi i d}

end FoundationsRL.DECLower


