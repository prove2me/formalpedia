-- Prove2me | Definitions.Def_actuarial_retainedExcessLoss
-- name    : actuarial_retainedExcessLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:30:47.247956+00:00
-- url     : https://prove2.me/theorems/e051d94e-5f26-41d0-8626-cb792e532ec0
-- title:
--   Insurer's retained loss under excess-of-loss reinsurance
-- statement:
--   Retained claim amount under a nonnegative retention limit a: the insurer pays the smaller of claim z and retention a.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)=\min(z,a)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def retainedExcessLoss (z a : ℝ) : ℝ := min z a

end ActuarialValuation


