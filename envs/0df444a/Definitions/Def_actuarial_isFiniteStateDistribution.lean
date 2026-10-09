-- Prove2me | Definitions.Def_actuarial_isFiniteStateDistribution
-- name    : actuarial_isFiniteStateDistribution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:06:43.588735+00:00
-- url     : https://prove2.me/theorems/395233ee-17cd-477a-8434-dbb5c213474f
-- title:
--   Probability distribution over a finite state set
-- statement:
--   State-occupation probabilities are nonnegative and have unit total mass.
--
--   **Mathematical statement**
--
--   $$
--   \mu_i\ge0,\quad\sum_i\mu_i=1
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def isFiniteStateDistribution {S : Type*} [Fintype S]
  (μ : S → ℝ) : Prop :=
  (∀ i : S, 0 ≤ μ i) ∧ (∑ i : S, μ i) = 1

end ActuarialValuation


