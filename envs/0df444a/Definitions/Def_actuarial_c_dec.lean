-- Prove2me | Definitions.Def_actuarial_c_dec
-- name    : actuarial_c_dec
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:22:02.506453+00:00
-- url     : https://prove2.me/theorems/7ed16e22-4ad0-413e-b748-1e3ba819173f
-- title:
--   decreasing death benefit
-- statement:
--   decreasing death benefit.
--
--   Mathematical relation:
--
--   $$
--   b_j=n-j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def dec (n j : ℕ) : ℝ := (n-j : ℕ)
end ActuarialAssurances


