-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_logLoss
-- name    : FoundationsRL_StatLearning_logLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:19.245978+00:00
-- url     : https://prove2.me/theorems/c7198663-5e4f-499f-bf6d-2eab78688f1d
-- title:
--   Logarithmic loss
-- statement:
--   For a distribution $p$ on $\mathcal Y$ with density $p(\cdot)$, the **logarithmic loss** of the outcome $y$ is
--
--   $$
--   \ell_{\log}(p,y)=-\log p(y).
--   $$
--
--   It is the loss of conditional density estimation.
--
--   **Formalization Note** Lean's `Real.log 0` is $0$, while the true loss at $p(y)=0$ is $+\infty$, so theorems evaluating this loss in expectation state $p(y)>0$ almost surely.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, (1.2), p. 7

import Mathlib

namespace FoundationsRL.StatLearning

/-- **Logarithmic loss** `ℓ_log(p, y) = −log p(y)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, (1.2), p. 7.

**Formalization Note.** A prediction `p` is a density on `Y` (`FoundationsRL.StatLearning.IsCondDensity`
says with respect to which measure). `Real.log 0 = 0` in Lean, whereas the true loss at `p y = 0` is
`+∞`, so every theorem evaluating this loss in expectation states that `p y > 0` almost surely. -/
noncomputable def logLoss {Y : Type*} (p : Y → ℝ) (y : Y) : ℝ :=
  -Real.log (p y)

end FoundationsRL.StatLearning


