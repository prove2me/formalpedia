-- Prove2me | Definitions.Def_actuarial_c_pure
-- name    : actuarial_c_pure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:18:22.276255+00:00
-- url     : https://prove2.me/theorems/2f074178-6f9a-4e8b-8b78-ab8ff38c5bab
-- title:
--   expected realised maturity benefit
-- statement:
--   expected realised maturity benefit.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[v^n\mathbf{1}_{\{K\ge n\}}]
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_purePath

namespace ActuarialAssurances

noncomputable def pure (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*purePath n k v
end ActuarialAssurances


