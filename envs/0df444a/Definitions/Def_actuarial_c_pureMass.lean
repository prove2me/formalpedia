-- Prove2me | Definitions.Def_actuarial_c_pureMass
-- name    : actuarial_c_pureMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:18:52.530706+00:00
-- url     : https://prove2.me/theorems/07307c18-286c-4af8-bf48-95ca9a763447
-- title:
--   independent pure endowment
-- statement:
--   independent pure endowment.
--
--   Mathematical relation:
--
--   $$
--   v^nS(n)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

namespace ActuarialAssurances

noncomputable def pureMass (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : ℝ := v^n*surv h p n
end ActuarialAssurances


