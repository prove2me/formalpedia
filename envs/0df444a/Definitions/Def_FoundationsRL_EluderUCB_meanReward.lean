-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_meanReward
-- name    : FoundationsRL_EluderUCB_meanReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:40.046872+00:00
-- url     : https://prove2.me/theorems/caf43c54-36bd-4807-aee2-65b5fd8ff89f
-- title:
--   (4.2): the mean reward function $f^\star$
-- statement:
--   For a model $M^\star$ that assigns to each decision $\pi$ a law $M^\star(\cdot\mid\pi)$ on rewards, the mean reward function is
--
--   $$
--   f^\star(\pi):=\mathbb E[r\mid\pi],\qquad r\sim M^\star(\cdot\mid\pi).
--   $$
--
--   **Formalization Note** $M^\star$ is a kernel from decisions to real numbers. The theorems of this mission assume each $M^\star(\cdot\mid\pi)$ is carried by $[0,1]$, so the integral is that of a bounded function.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.2), p. 57

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.EluderUCB

/-- **The mean reward function.** Foster & Rakhlin, arXiv:2312.16730v1, (4.2), p. 57:
`f⋆(π) := E[r | π]` for `r ∼ M⋆(· | π)`.

**Formalization Note.** `f⋆` is computed from the model `M⋆`, here a kernel from decisions to real
rewards. The theorems assume `M⋆(· | π)` is carried by `[0, 1]`, so the integral is that of a
bounded function. -/
noncomputable def meanReward {Act : Type*} [MeasurableSpace Act] (M : Kernel Act ℝ) (p : Act) : ℝ :=
  ∫ y, y ∂(M p)

end FoundationsRL.EluderUCB


