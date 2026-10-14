-- Prove2me | Definitions.Def_actuarial_c_endowVariance
-- name    : actuarial_c_endowVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:32:57.497386+00:00
-- url     : https://prove2.me/theorems/2ab970be-f268-4fab-9b8f-2fea532eff65
-- title:
--   Variance of actual endowment present value
-- statement:
--   Variance of actual endowment present value.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z_{\text{end}})=\mathbb E[Z_{\text{end}}^2]-\mathbb E[Z_{\text{end}}]^2
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_endowSecond

namespace ActuarialAssurances

noncomputable def endowVariance (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := endowSecond h n v b p-(endow h n v b p)^2
end ActuarialAssurances


