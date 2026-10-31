-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_sqLoss
-- name    : FoundationsRL_StatLearning_sqLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:14.215747+00:00
-- url     : https://prove2.me/theorems/e1a11fa5-030d-4242-931c-fd4e01632c4a
-- title:
--   Square loss
-- statement:
--   The **square loss** on $\mathcal Y=\mathcal Y'=\mathbb R$ is
--
--   $$
--   \ell(a,b)=(a-b)^2.
--   $$
--
--   It is the loss of regression, for which the mission proves the fast rate.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, p. 7

import Mathlib

namespace FoundationsRL.StatLearning

/-- **Square loss** `ℓ(a, b) = (a − b)²`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, p. 7. -/
def sqLoss (a b : ℝ) : ℝ :=
  (a - b) ^ 2

end FoundationsRL.StatLearning


