-- Prove2me | Definitions.Def_actuarial_expectedRetainedLoss
-- name    : actuarial_expectedRetainedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:32:49.977564+00:00
-- url     : https://prove2.me/theorems/53f322ed-51e0-49c0-a257-3374996a089f
-- title:
--   Finite-scenario expected retained claim amount
-- statement:
--   Probability-weighted retained insurance claims across finitely many scenarios; valid expectation if weights are nonnegative and sum to one.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[r(Z,a)]=\sum_\omega w_\omega\min(z_\omega,a)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

noncomputable def expectedRetainedLoss {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (z : Ω → ℝ) (a : ℝ) : ℝ :=
  ∑ ω : Ω, w ω * retainedExcessLoss (z ω) a

end ActuarialValuation


