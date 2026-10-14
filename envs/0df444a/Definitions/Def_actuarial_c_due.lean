-- Prove2me | Definitions.Def_actuarial_c_due
-- name    : actuarial_c_due
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:20:23.217549+00:00
-- url     : https://prove2.me/theorems/8722edf0-82ad-4c69-bdc6-b5e476f80aa4
-- title:
--   temporary premium annuity-due EPV
-- statement:
--   temporary premium annuity-due EPV.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_n=\sum_{j=0}^{n-1}v^jS(j)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

namespace ActuarialAssurances

noncomputable def due (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range n, v^j*surv h p j
end ActuarialAssurances


