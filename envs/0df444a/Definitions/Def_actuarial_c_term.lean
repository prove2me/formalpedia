-- Prove2me | Definitions.Def_actuarial_c_term
-- name    : actuarial_c_term
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:16:10.234562+00:00
-- url     : https://prove2.me/theorems/5b88db4d-97cc-4e1d-83c8-89d2a3af3902
-- title:
--   temporary death-assurance EPV
-- statement:
--   temporary death-assurance EPV.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{n|}=\mathbb{E}[Z_n]
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath

namespace ActuarialAssurances

noncomputable def term (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*termPath h n v b k
end ActuarialAssurances


