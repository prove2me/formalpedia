-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_bayesRegret
-- name    : FoundationsRL_PosteriorSampling_bayesRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:14.506022+00:00
-- url     : https://prove2.me/theorems/aeb24fc1-1c53-499b-9974-6d3d5be45c01
-- title:
--   Bayesian regret $\mathrm{Reg}_{\mathsf{Bayes}}(\mu)$
-- statement:
--   The **Bayesian regret** of an algorithm over $T$ rounds under the prior $\mu$ is the regret averaged over the prior,
--
--   $$
--   \mathrm{Reg}_{\mathsf{Bayes}}(\mu)=\mathbb E_{M^\star\sim\mu}\,\mathbb E^{M^\star}[\mathrm{Reg}]=\mathbb E\Big[\sum_{t=1}^T\big(f^\star(\pi^\star)-f^\star(\pi^t)\big)\Big],
--   $$
--
--   the last expectation being under the joint law of $(M^\star,H^T)$.
--
--   **Formalization Note** The term $\mathbb E_{\pi^t\sim p^t}[f^\star(\pi^t)]$ of the regret is written as $f^\star(\pi^t)$ under the outer expectation, as the source does on p. 35. The integrand is integrable as soon as the mean rewards are integrable under $\mu$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 30, with Reg from Eq. (2.3), p. 22, and the form on p. 35

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_OptimalSelection
import Definitions.Def_FoundationsRL_PosteriorSampling_jointLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- The Bayesian regret `Reg_Bayes(μ) = E_{M⋆∼μ} E^{M⋆}[Reg]` of `π` over `T` rounds (Foster &
Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, p. 30, with `Reg` from Eq. (2.3), p. 22): the expectation under the joint law
of `(M⋆, H^T)` of `∑_{t=1}^T (f⋆(π⋆) − f⋆(πᵗ))`, the form the book uses on p. 35.

**Formalization Note.** The book's `E_{πᵗ∼pᵗ}[f⋆(πᵗ)]` inside `Reg` is replaced by `f⋆(πᵗ)` under
the outer expectation, which is the same number. The integrand is measurable, and integrable as
soon as the mean rewards are integrable under `μ` (the hypothesis of every statement about this
quantity, implied by bounded rewards), so the Bochner integral is the true expectation. -/
noncomputable def bayesRegret {A : ℕ} (μ : Measure (BanditModel A)) (sel : OptimalSelection A)
    (π : BanditPolicy A) (T : ℕ) : ℝ :=
  ∫ p, ∑ t : Fin T, (meanReward p.1 (sel.toFun p.1) - meanReward p.1 (p.2 t).1) ∂jointLaw μ π T

end FoundationsRL.PosteriorSampling


