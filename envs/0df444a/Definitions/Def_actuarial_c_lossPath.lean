-- Prove2me | Definitions.Def_actuarial_c_lossPath
-- name    : actuarial_c_lossPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:35:40.465319+00:00
-- url     : https://prove2.me/theorems/dedc78d3-4fba-4073-bea8-05f941b68a24
-- title:
--   Actual present value of insurer loss, claims less premiums
-- statement:
--   Actual present value of insurer loss, claims less premiums.
--
--   Mathematical relation:
--
--   $$
--   L(k)=Z_n(k)-PY_n(k)
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_premiumPath

namespace ActuarialAssurances

noncomputable def lossPath (h n : ℕ) (v premium : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := termPath h n v b k-premium*premiumPath n v k
end ActuarialAssurances


