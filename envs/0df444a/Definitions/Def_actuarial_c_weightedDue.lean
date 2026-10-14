-- Prove2me | Definitions.Def_actuarial_c_weightedDue
-- name    : actuarial_c_weightedDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:11.293743+00:00
-- url     : https://prove2.me/theorems/a5453365-9dcd-4e3c-a7ca-fd7e2d77e768
-- title:
--   Survival-contingent annuity weighted by the death-benefit vector
-- statement:
--   Survival-contingent annuity weighted by the death-benefit vector.
--
--   Mathematical relation:
--
--   $$
--   \ddot a(b)=\sum_{j=0}^{h-1}b_jv^jS(j)
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, death-year and survival cashflow encoding, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

namespace ActuarialAssurances

noncomputable def weightedDue (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, b j*v^j*surv h p j
end ActuarialAssurances


