-- Prove2me | Definitions.Def_actuarial_c_geom
-- name    : actuarial_c_geom
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:24:31.795025+00:00
-- url     : https://prove2.me/theorems/f9d455b6-a044-4583-aaac-3cbc473ca2a9
-- title:
--   geometric death benefit
-- statement:
--   geometric death benefit.
--
--   Mathematical relation:
--
--   $$
--   b_j=r^j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances

noncomputable def geom (r : ℝ) (j : ℕ) : ℝ := r^j
end ActuarialAssurances


