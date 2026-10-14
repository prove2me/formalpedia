-- Prove2me | Definitions.Def_actuarial_c_massPV
-- name    : actuarial_c_massPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:15:37.351019+00:00
-- url     : https://prove2.me/theorems/dfb93992-0430-49da-91bd-d17d8960057a
-- title:
--   death-probability sum
-- statement:
--   death-probability sum.
--
--   Mathematical relation:
--
--   $$
--   \sum_{j=0}^{h-1}v^{j+1}b_jp_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def massPV (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, v^(j+1)*b j*p j
end ActuarialAssurances


