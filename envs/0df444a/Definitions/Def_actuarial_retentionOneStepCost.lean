-- Prove2me | Definitions.Def_actuarial_retentionOneStepCost
-- name    : actuarial_retentionOneStepCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T06:06:41.258834+00:00
-- url     : https://prove2.me/theorems/ce174aa1-7414-4cef-bebc-b6836f87e7f6
-- title:
--   One-year retained claims plus reinsurance premium
-- statement:
--   Expected annual retained claims plus deterministic reinsurance premium at retention a.
--
--   **Mathematical statement**
--
--   $$
--   C(a)=q(a)+\mathbb E[\min(Z,a)]
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
open MeasureTheory

namespace ActuarialValuation

noncomputable def retentionOneStepCost {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (z : Ω → ℝ) (q : ℝ → ℝ) (a : ℝ) : ℝ :=
  expectedRetainedLoss w z a + q a

end ActuarialValuation


