-- Prove2me | Definitions.Def_actuarial_transitionStageReward
-- name    : actuarial_transitionStageReward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:09:50.862989+00:00
-- url     : https://prove2.me/theorems/9b27767f-2892-410a-9790-87400f1657cc
-- title:
--   Expected benefit from a one-year state transition
-- statement:
--   Expected benefit paid at the end of a year on each i-to-j transition, before discounting.
--
--   **Mathematical statement**
--
--   $$
--   R^{\rm tr}=\sum_{i,j}\mu_iP_{ij}b_{ij}
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def transitionStageReward {S : Type*} [Fintype S]
  (μ : S → ℝ) (P : S → S → ℝ)
  (b : S → S → ℝ) : ℝ :=
  ∑ i : S, ∑ j : S, μ i * P i j * b i j

end ActuarialValuation


