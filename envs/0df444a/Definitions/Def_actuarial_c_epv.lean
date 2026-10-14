-- Prove2me | Definitions.Def_actuarial_c_epv
-- name    : actuarial_c_epv
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:15:30.520184+00:00
-- url     : https://prove2.me/theorems/3594d9fc-26ff-49f7-b827-ec5ad07ed566
-- title:
--   expectation from death-state cashflows
-- statement:
--   expectation from death-state cashflows.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z]=\sum_{k=0}^{h}p_kZ(k)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

namespace ActuarialAssurances

noncomputable def epv (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*path h v b k
end ActuarialAssurances


