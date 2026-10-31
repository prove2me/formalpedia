-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_infoGain
-- name    : FoundationsRL_PosteriorSampling_infoGain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:46.614636+00:00
-- url     : https://prove2.me/theorems/67a5d03a-c4a6-4c18-a04e-f3fd23a08a89
-- title:
--   Information gains about $\pi^\star$ at a round
-- statement:
--   Three quantities measure what a round reveals about $\pi^\star$. At a history $H^{t-1}$,
--
--   $$
--   \mathbb E_{t-1}\big[D_{\mathsf{KL}}(P_{r^t\mid\pi^\star,\pi^t,H^{t-1}}\,\|\,P_{r^t\mid\pi^t,H^{t-1}})\big]
--   \quad\text{and}\quad
--   \mathbb E_{t-1}\big[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})\big],
--   $$
--
--   and, averaging the second over the history, $\mathbb E[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})]$.
--
--   **Formalization Note** Values lie in $[0,\infty]$. Since $H^t=(H^{t-1},\pi^t,r^t)$, the source's $P_{\pi^\star\mid\pi^t,r^t,H^{t-1}}$ and $P_{\pi^\star\mid H^t}$ are the same object here.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (2.33) and the displays around it, p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_posterior
import Definitions.Def_FoundationsRL_PosteriorSampling_roundLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm InformationTheory
open scoped ENNReal

namespace FoundationsRL.PosteriorSampling

variable {A : ℕ} [NeZero A] (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ]
  (sel : OptimalSelection A) (π : BanditPolicy A)

/-- `E_{t-1}[D_KL(P_{r|π⋆,π,H^{t-1}} ∥ P_{r|π,H^{t-1}})]` (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, p. 36): the
expected divergence between the reward law given `π⋆` and without it, at history `h`.

**Formalization Note.** Values in `ℝ≥0∞`; `InformationTheory.klDiv` is `∞` when absolute
continuity or integrability of the log-likelihood ratio fails. -/
noncomputable def rewardInfoGain (t : ℕ) (h : BanditHistory A t) : ℝ≥0∞ :=
  ∫⁻ z, klDiv (rewardGiven μ sel π t h z.1 z.2.2.1) (rewardMarginal μ sel π t h z.1)
    ∂roundLaw μ sel π t h

/-- `E_{t-1}[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})]` (Foster & Rakhlin, arXiv:2312.16730v1, Eq. (2.33),
p. 36) at history `h`: the expected divergence between the posterior of `π⋆` after the round and
before it.

**Formalization Note.** `H^t = (H^{t-1}, πᵗ, rᵗ)` is `appendRound`, so the book's
`P_{π⋆|πᵗ,rᵗ,H^{t-1}}` and `P_{π⋆|H^t}` are the same object here. -/
noncomputable def posteriorInfoGain (t : ℕ) (h : BanditHistory A t) : ℝ≥0∞ :=
  ∫⁻ z, klDiv (optPosterior μ sel π (t + 1) (appendRound h (z.1, z.2.1)))
    (optPosterior μ sel π t h) ∂roundLaw μ sel π t h

/-- `E[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})]` (Foster & Rakhlin, arXiv:2312.16730v1, §2.6, p. 36):
the information about `π⋆` acquired at round `t + 1`. -/
noncomputable def expectedInfoGain (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ h, posteriorInfoGain μ sel π t h ∂histLaw μ π t

end FoundationsRL.PosteriorSampling


