-- Prove2me | Definitions.Def_actuarial_c_total
-- name    : actuarial_c_total
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:13:17.758209+00:00
-- url     : https://prove2.me/theorems/4b52fa2d-5067-42f3-8bc9-6a76dcca5cc9
-- title:
--   finite state mass
-- statement:
--   finite state mass.
--
--   Mathematical relation:
--
--   $$
--   \sum_{j=0}^{h}p_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def total (h : ℕ) (p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k
end ActuarialAssurances


