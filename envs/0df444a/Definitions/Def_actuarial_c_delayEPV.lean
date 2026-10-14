-- Prove2me | Definitions.Def_actuarial_c_delayEPV
-- name    : actuarial_c_delayEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:51.499039+00:00
-- url     : https://prove2.me/theorems/79da5027-8e1c-4c6b-8403-77385659f5e8
-- title:
--   Expectation of delayed claim payments over the lifetime states
-- statement:
--   Expectation of delayed claim payments over the lifetime states.
--
--   Mathematical relation:
--
--   $$
--   A_r=\mathbb E[Z_r]
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_delayPath

namespace ActuarialAssurances

noncomputable def delayEPV (h lag : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*delayPath h lag v b k
end ActuarialAssurances


