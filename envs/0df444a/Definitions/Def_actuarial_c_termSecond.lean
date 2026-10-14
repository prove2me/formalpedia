-- Prove2me | Definitions.Def_actuarial_c_termSecond
-- name    : actuarial_c_termSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:29:00.91899+00:00
-- url     : https://prove2.me/theorems/a116d770-3222-4e6a-99f3-1f1144066ed9
-- title:
--   Second moment of actual temporary death assurance PV
-- statement:
--   Second moment of actual temporary death assurance PV.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_n^2]=\sum_kp_kZ_n(k)^2
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath

namespace ActuarialAssurances

noncomputable def termSecond (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*(termPath h n v b k)^2
end ActuarialAssurances


