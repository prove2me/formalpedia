-- Prove2me | Definitions.Def_actuarial_poissonCountConvolution
-- name    : actuarial_poissonCountConvolution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:51:58.667514+00:00
-- url     : https://prove2.me/theorems/36be4977-9337-4d88-8d9b-736c598bcc25
-- title:
--   Finite convolution of two Poisson count laws
-- statement:
--   For an aggregate count n, the finite sum evaluates every allocation of arrivals between two independent Poisson streams of respective rates a and b. The algebra encodes independence by multiplying count coefficients before summing over all possible splits.
--
--   **Mathematical statement**
--
--   $$
--   h_n=\sum_{k=0}^{n}p_a(k)p_b(n-k)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

noncomputable def poissonCountConvolution (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    poissonCountMass a k * poissonCountMass b (n - k)

end ActuarialValuation


