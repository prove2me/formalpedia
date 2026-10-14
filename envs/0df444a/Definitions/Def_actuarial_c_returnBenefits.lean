-- Prove2me | Definitions.Def_actuarial_c_returnBenefits
-- name    : actuarial_c_returnBenefits
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:49.907986+00:00
-- url     : https://prove2.me/theorems/8a855698-f4b7-4c51-9f89-55715753d080
-- title:
--   Premium-refund amount accumulated only as nominal paid instalments
-- statement:
--   Premium-refund amount accumulated only as nominal paid instalments.
--
--   Mathematical relation:
--
--   $$
--   b_j=P(j+1)
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def returnBenefits (premium : ℝ) (j : ℕ) : ℝ := premium*(j+1 : ℕ)
end ActuarialAssurances


