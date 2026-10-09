-- Prove2me | Definitions.Def_actuarial_poissonSplitJointMass
-- name    : actuarial_poissonSplitJointMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:53:24.722153+00:00
-- url     : https://prove2.me/theorems/322387fc-19c7-400b-9509-a8953854cbe9
-- title:
--   Joint count coefficient under independent Bernoulli marking
-- statement:
--   The unlabelled total count is selected plus other. Conditional on that total, independent cause marking produces the binomial coefficient, selected-fraction power and complementary-fraction power. This is a joint count mass, not an assumption that independently thinned streams already exist.
--
--   **Mathematical statement**
--
--   $$
--   J(a,b)=p_\lambda(a+b){a+b\choose a}p^a(1-p)^b
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

noncomputable def poissonSplitJointMass
  (rate selection : ℝ) (selected other : ℕ) : ℝ :=
  poissonCountMass rate (selected + other) *
    (Nat.choose (selected + other) selected : ℝ) *
    selection ^ selected * (1 - selection) ^ other

end ActuarialValuation


