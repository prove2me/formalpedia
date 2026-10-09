-- Prove2me | Definitions.Def_actuarial_occupationStageReward
-- name    : actuarial_occupationStageReward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:10:08.476351+00:00
-- url     : https://prove2.me/theorems/955cd003-72f4-470e-bff6-a47b2b97e192
-- title:
--   Expected payment for occupying a state
-- statement:
--   Expected payment at the beginning of a year according to the state occupied then.
--
--   **Mathematical statement**
--
--   $$
--   R^{\rm occ}=\sum_i\mu_i c_i
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def occupationStageReward {S : Type*} [Fintype S]
  (μ c : S → ℝ) : ℝ :=
  ∑ i : S, μ i * c i

end ActuarialValuation


