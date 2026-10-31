-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_meanReward
-- name    : FoundationsRL_LinUCB_meanReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:16.266003+00:00
-- url     : https://prove2.me/theorems/2f3f80a8-e9fd-4520-9fe5-a1a04176ad7e
-- title:
--   Mean reward function $f^\star(x,\pi)$
-- statement:
--   The **mean reward function** of the model $M^\star$ is
--
--   $$
--   f^\star(x,\pi)=\mathbb E[r\mid x,\pi]=\int r\,M^\star(dr\mid x,\pi).
--   $$
--
--   It is the object the learner tries to estimate, and regret is measured against it.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.2), p. 39

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- The mean reward function `f⋆(x, π) := E[r | x, π]`, `r ∼ M⋆(· | x, π)` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.2), p. 39). -/
noncomputable def meanReward {X Act : Type*} [MeasurableSpace X] [MeasurableSpace Act]
    (Mstar : Kernel (X × Act) ℝ) (x : X) (a : Act) : ℝ :=
  ∫ r, r ∂(Mstar (x, a))

end FoundationsRL.LinUCB


