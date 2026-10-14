-- Prove2me | Definitions.Def_actuarial_c_variance
-- name    : actuarial_c_variance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:21.99446+00:00
-- url     : https://prove2.me/theorems/c7f14f45-1bd7-4d7f-a967-e5be8bb23fe3
-- title:
--   random PV variance
-- statement:
--   random PV variance.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z)=\mathbb{E}[Z^2]-\mathbb{E}[Z]^2
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_second

namespace ActuarialAssurances

noncomputable def variance (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := second h v b p-(epv h v b p)^2
end ActuarialAssurances


