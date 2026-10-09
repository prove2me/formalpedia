-- Prove2me | Definitions.Def_actuarial_nextStateMass
-- name    : actuarial_nextStateMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:09:34.849183+00:00
-- url     : https://prove2.me/theorems/43e19cea-289e-4931-8e9b-2624e00015ab
-- title:
--   One-step distribution propagation
-- statement:
--   Distribution mass at state j after one transition is summed over all initial states.
--
--   **Mathematical statement**
--
--   $$
--   \mu'_j=\sum_i\mu_iP_{ij}
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def nextStateMass {S : Type*} [Fintype S]
  (μ : S → ℝ) (P : S → S → ℝ) (j : S) : ℝ :=
  ∑ i : S, μ i * P i j

end ActuarialValuation


