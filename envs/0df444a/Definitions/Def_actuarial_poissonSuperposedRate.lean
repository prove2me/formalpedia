-- Prove2me | Definitions.Def_actuarial_poissonSuperposedRate
-- name    : actuarial_poissonSuperposedRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:53:38.508463+00:00
-- url     : https://prove2.me/theorems/c79d16d5-f4b1-4c36-b6cb-fc842ec2584b
-- title:
--   Combined frequency of independent Poisson streams
-- statement:
--   The superposed frequency is the sum of the arrival intensities of two independent claim classes. When the component rates are nonnegative, so is this total frequency, and the combined count distribution will be shown to follow a Poisson law.
--
--   **Mathematical statement**
--
--   $$
--   \lambda_{\rm total}=\lambda_1+\lambda_2
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib

namespace ActuarialValuation

noncomputable def poissonSuperposedRate (first second : ℝ) : ℝ :=
  first + second

end ActuarialValuation


