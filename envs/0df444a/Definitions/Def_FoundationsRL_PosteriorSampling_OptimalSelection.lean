-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_OptimalSelection
-- name    : FoundationsRL_PosteriorSampling_OptimalSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:14.724077+00:00
-- url     : https://prove2.me/theorems/1f792458-4dd5-40f2-991e-f43097dbf5a2
-- title:
--   A measurable selection of $\arg\max_\pi f^M(\pi)$
-- statement:
--   A **measurable optimal selection** assigns to each model $M$ a decision $\pi_M\in\arg\max_{\pi} f^M(\pi)$, in such a way that $M\mapsto\pi_M$ is measurable. Under a prior, $\pi^\star=\pi_{M^\star}$ is then a random variable.
--
--   **Formalization Note** The source writes $\arg\max$ without a tie-breaking rule. Keeping the selection as a parameter covers every rule; the minimal-index rule is one instance.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 22 (π⋆ := arg max f⋆) and p. 31 (π⋆ = π_{f⋆})

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_BanditModel

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.PosteriorSampling

/-- A measurable selection of `π_M ∈ arg max_π f^M(π)` (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 22 and p. 31,
`π⋆ = π_{f⋆}`).

**Formalization Note.** The book writes `arg max` without a tie-breaking rule. Taking any
measurable selection as a parameter covers every such rule; the minimal-index rule is one
instance. Measurability is what makes `π⋆` a random variable under the prior. -/
structure OptimalSelection (A : ℕ) where
  /-- The optimal decision `π_M` of the model `M`. -/
  toFun : BanditModel A → Fin A
  /-- `π⋆ = π_{M⋆}` is a random variable. -/
  measurable : Measurable toFun
  /-- `π_M` maximizes the mean reward of `M`. -/
  isOptimal : ∀ M a, meanReward M a ≤ meanReward M (toFun M)

end FoundationsRL.PosteriorSampling


