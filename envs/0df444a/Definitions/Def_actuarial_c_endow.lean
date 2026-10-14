-- Prove2me | Definitions.Def_actuarial_c_endow
-- name    : actuarial_c_endow
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:19:56.162986+00:00
-- url     : https://prove2.me/theorems/08ae4585-ba14-4979-86f9-457973c1b9be
-- title:
--   endowment assurance EPV
-- statement:
--   endowment assurance EPV.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z_{\text{end}}]
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath

namespace ActuarialAssurances

noncomputable def endow (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*endowPath h n v b k
end ActuarialAssurances


