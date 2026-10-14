-- Prove2me | Definitions.Def_actuarial_c_increasingDue
-- name    : actuarial_c_increasingDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:24.169972+00:00
-- url     : https://prove2.me/theorems/fc4d8b43-9166-47f2-8e17-7ad767fc0ca1
-- title:
--   Increasing temporary annuity-due from the same survival tail
-- statement:
--   Increasing temporary annuity-due from the same survival tail.
--
--   Mathematical relation:
--
--   $$
--   I\ddot a=\sum_{j=0}^{h-1}(j+1)v^jS(j)
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

noncomputable def increasingDue (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, (j+1 : ℕ)*v^j*surv h p j
end ActuarialAssurances


