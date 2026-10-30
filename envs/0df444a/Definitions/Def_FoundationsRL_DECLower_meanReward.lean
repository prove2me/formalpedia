-- Prove2me | Definitions.Def_FoundationsRL_DECLower_meanReward
-- name    : FoundationsRL_DECLower_meanReward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:20.844301+00:00
-- url     : https://prove2.me/theorems/fc1fae16-f799-460c-ad34-235a42600814
-- title:
--   Mean reward function $f^M(\pi)=\mathbb E_{M,\pi}[r]$
-- statement:
--   For a kernel $M:\Pi\to\Delta(\mathbb R\times\mathcal O)$ and a decision $\pi\in\Pi$, the **mean reward** is
--
--   $$
--   f^M(\pi)=\mathbb E_{(r,o)\sim M(\pi)}[r].
--   $$
--
--   For a model (rewards in $[0,1]$) it lies in $[0,1]$. It defines the regret (6.3) and the constrained Decision-Estimation Coefficient.
--
--   **Formalization Note** A Bochner integral of the reward coordinate; for a model the integrand is bounded, so the integral is the expectation.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.1, p. 94 (mean reward function)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Mean reward function** `f^M(π) := E_{M,π}[r]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.1, p. 94.

`meanReward M d` is the expectation of the reward coordinate `r` under `(r, o) ∼ M(d)`.

**Formalization Note.** A Bochner integral; for a model (`IsModel`) the reward lies in `[0, 1]`
almost surely, so the integrand is integrable and the value is the paper's `f^M(π) ∈ [0, 1]`. -/
noncomputable def meanReward {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (M : Kernel D (ℝ × O)) (d : D) : ℝ :=
  ∫ z, z.1 ∂(M d)

end FoundationsRL.DECLower


