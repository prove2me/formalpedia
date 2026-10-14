-- Prove2me | Definitions.Def_actuarial_c_differenceBenefit
-- name    : actuarial_c_differenceBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:37.671855+00:00
-- url     : https://prove2.me/theorems/afb98a07-1b10-45ba-83a9-e9225992e4ee
-- title:
--   Finite benefit-vector increment and survival boundary sum
-- statement:
--   Finite benefit-vector increment and survival boundary sum.
--
--   Mathematical relation:
--
--   $$
--   b_0S(0)+\sum_{j=1}^{h-1}(b_j-b_{j-1})v^jS(j)
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

noncomputable def differenceBenefit (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := b 0*surv h p 0+∑ j ∈ Finset.range (h-1), (b (j+1)-b j)*v^(j+1)*surv h p (j+1)
end ActuarialAssurances


