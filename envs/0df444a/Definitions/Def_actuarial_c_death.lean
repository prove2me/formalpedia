-- Prove2me | Definitions.Def_actuarial_c_death
-- name    : actuarial_c_death
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:13:03.441989+00:00
-- url     : https://prove2.me/theorems/016d0b07-8a46-4d75-8976-b5a3004712df
-- title:
--   death-year indicator
-- statement:
--   death-year indicator.
--
--   Mathematical relation:
--
--   $$
--   \mathbf{1}_{\{K=j\}}
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def death (k j : ℕ) : ℝ := if k = j then 1 else 0
end ActuarialAssurances


