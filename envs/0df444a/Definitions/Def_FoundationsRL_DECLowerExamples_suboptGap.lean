-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_suboptGap
-- name    : FoundationsRL_DECLowerExamples_suboptGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:35.017993+00:00
-- url     : https://prove2.me/theorems/93d08f58-ea11-4ce9-a1ff-2acff29b3a2a
-- title:
--   Suboptimality gap $f^M(\pi_M)-f^M(\pi)\in[0,\infty]$
-- statement:
--   Let $M:\Pi\to\Delta(\mathbb R\times\mathcal O)$ be a model and $f^M(\pi)=\mathbb E_{(r,o)\sim M(\pi)}[r]$ its mean reward function. The **suboptimality gap** of a decision $\pi$ is
--   $$
--   f^M(\pi_M)-f^M(\pi)=\sup_{\pi'\in\Pi}\bigl(f^M(\pi')-f^M(\pi)\bigr)\in[0,\infty],
--   $$
--   where $\pi_M=\arg\max_{\pi}f^M(\pi)$ is the optimal decision of $M$.
--
--   It is the regret of playing $\pi$ when $M$ is the true model, and the objective of the constrained Decision-Estimation Coefficient.
--
--   **Formalization Note** The mean reward is the published `FoundationsRL.DECLower.meanReward`. The argmax is replaced by a supremum, which agrees with it whenever the maximum is attained. The gap is computed in $[0,\infty]$, because Proposition 30 and Examples 6.4–6.5 assume no reward range: a mean reward that is unbounded above gives the gap $+\infty$ rather than a default value.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.1, p. 94 (f^M, π_M) and §6.5.1, p. 104

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_meanReward

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLowerExamples

/-- **Suboptimality gap with values in `[0, ∞]`** `f^M(π_M) − f^M(π)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.1, p. 94 (`f^M(π) := E_{M,π}[r]`, `π_M := arg max_π f^M(π)`), the
integrand of the constrained DEC, §6.5.1, p. 104.

`suboptGap M d = sup_{d'} (f^M(d') − f^M(d))`, computed in `ℝ≥0∞`.

**Formalization Note.** `f^M` is the published mean reward `FoundationsRL.DECLower.meanReward`
(a Bochner integral of the reward coordinate). `π_M` is an argmax; `f^M(π_M) − f^M(π)` is
`sup_{π'} f^M(π') − f^M(π)` whenever the maximum is attained, and every term
`f^M(d') − f^M(d)` with `d' = d` is `0`, so the supremum is `≥ 0`. It is taken in `ℝ≥0∞`: no
reward range is assumed (Gaussian rewards in Examples 6.4–6.5), and a mean-reward function that is
unbounded above gives the gap `+∞` instead of a junk value. -/
noncomputable def suboptGap {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (M : Kernel D (ℝ × O)) (d : D) : ℝ≥0∞ :=
  ⨆ d', ENNReal.ofReal (FoundationsRL.DECLower.meanReward M d' - FoundationsRL.DECLower.meanReward M d)

end FoundationsRL.DECLowerExamples


