-- Prove2me | Definitions.Def_actuarial_c_netPremium
-- name    : actuarial_c_netPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:45:57.762121+00:00
-- url     : https://prove2.me/theorems/0410f539-a855-4a11-848e-ff56fa2cbb8b
-- title:
--   Net level premium by actuarial equivalence ratio
-- statement:
--   Net level premium by actuarial equivalence ratio.
--
--   Mathematical relation:
--
--   $$
--   P_{\text{net}}=A_n/\ddot a_n
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_due

namespace ActuarialAssurances

noncomputable def netPremium (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := term h n v b p/due h n v p
end ActuarialAssurances


