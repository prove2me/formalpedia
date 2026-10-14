-- Prove2me | Definitions.Def_actuarial_c_surv
-- name    : actuarial_c_surv
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:14:04.110319+00:00
-- url     : https://prove2.me/theorems/acc4c225-ed7c-402c-8e95-62b8289c52a0
-- title:
--   survival probability
-- statement:
--   survival probability.
--
--   Mathematical relation:
--
--   $$
--   S(t)=\sum_{j=t}^{h}p_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

namespace ActuarialAssurances

noncomputable def surv (h : ℕ) (p : ℕ → ℝ) (t : ℕ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*alive k t
end ActuarialAssurances


