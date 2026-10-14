-- Prove2me | Definitions.Def_actuarial_c_second
-- name    : actuarial_c_second
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:25:10.298337+00:00
-- url     : https://prove2.me/theorems/0c4a79df-9cc3-4427-8410-9a4a3596dcc8
-- title:
--   actual claim second moment
-- statement:
--   actual claim second moment.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z^2]=\sum_{k=0}^{h}p_kZ(k)^2
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

namespace ActuarialAssurances

noncomputable def second (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*(path h v b k)^2
end ActuarialAssurances


