-- Prove2me | Definitions.Def_actuarial_c_deferred
-- name    : actuarial_c_deferred
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:17:05.914549+00:00
-- url     : https://prove2.me/theorems/2f7c8ad2-3c7a-45ac-befc-2b1f40dbc38b
-- title:
--   deferred term death assurance
-- statement:
--   deferred term death assurance.
--
--   Mathematical relation:
--
--   $$
--   {}_{a|}A^{1}_{n|}=\sum_{j=a}^{a+n-1}v^{j+1}b_jp_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def deferred (h a n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then v^(j+1)*b j*p j else 0
end ActuarialAssurances


