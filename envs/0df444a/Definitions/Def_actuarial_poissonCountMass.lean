-- Prove2me | Definitions.Def_actuarial_poissonCountMass
-- name    : actuarial_poissonCountMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:50:39.942433+00:00
-- url     : https://prove2.me/theorems/c1262d79-e9b3-462b-9bbf-ab399b82d293
-- title:
--   Poisson count probability coefficient
-- statement:
--   Defines the probability of exactly n arrivals for a Poisson rate. Nonnegative rate is needed to interpret this real-valued expression as a probability, but the factorial and exponential algebra can also be studied for arbitrary real input.
--
--   **Mathematical statement**
--
--   $$
--   p_\lambda(n)=e^{-\lambda}\lambda^n/n!
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib

namespace ActuarialValuation

noncomputable def poissonCountMass (rate : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ n / (Nat.factorial n : ℝ)

end ActuarialValuation


