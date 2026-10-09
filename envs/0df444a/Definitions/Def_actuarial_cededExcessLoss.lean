-- Prove2me | Definitions.Def_actuarial_cededExcessLoss
-- name    : actuarial_cededExcessLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:31:06.457983+00:00
-- url     : https://prove2.me/theorems/1d513f48-2d89-4a97-b1a7-25eb532a3401
-- title:
--   Claim loss ceded to the reinsurer
-- statement:
--   Difference between gross claim and retained amount, transferred to reinsurer under an excess-of-loss contract.
--
--   **Mathematical statement**
--
--   $$
--   c(z,a)=z-\min(z,a)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def cededExcessLoss (z a : ℝ) : ℝ := z - min z a

end ActuarialValuation


