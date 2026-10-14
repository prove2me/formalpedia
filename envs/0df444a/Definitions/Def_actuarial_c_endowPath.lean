-- Prove2me | Definitions.Def_actuarial_c_endowPath
-- name    : actuarial_c_endowPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:19:17.260212+00:00
-- url     : https://prove2.me/theorems/8698054c-14d6-45dc-806a-d1008bb2fd66
-- title:
--   mutually exclusive death or maturity benefit
-- statement:
--   mutually exclusive death or maturity benefit.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{end}}(k)=Z_n(k)+v^n\mathbf{1}_{\{k\ge n\}}
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath

namespace ActuarialAssurances

noncomputable def endowPath (h n : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := termPath h n v b k+purePath n k v
end ActuarialAssurances


