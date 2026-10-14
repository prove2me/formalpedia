-- Prove2me | Definitions.Def_actuarial_c_endowSecond
-- name    : actuarial_c_endowSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:30:51.849043+00:00
-- url     : https://prove2.me/theorems/346d0df1-99e8-411d-9338-ad18f376f887
-- title:
--   Second moment of mutually exclusive death/maturity endowment PV
-- statement:
--   Second moment of mutually exclusive death/maturity endowment PV.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_{\text{end}}^2]=\sum_kp_kZ_{\text{end}}(k)^2
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

namespace ActuarialAssurances

noncomputable def endowSecond (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*(endowPath h n v b k)^2
end ActuarialAssurances


