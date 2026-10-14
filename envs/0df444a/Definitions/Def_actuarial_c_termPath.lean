-- Prove2me | Definitions.Def_actuarial_c_termPath
-- name    : actuarial_c_termPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:15:56.359246+00:00
-- url     : https://prove2.me/theorems/e3938da1-f62e-4fa2-b1ac-f13a2cfb26fe
-- title:
--   term-assurance random PV
-- statement:
--   term-assurance random PV.
--
--   Mathematical relation:
--
--   $$
--   Z_n(k)=\sum_{j=0}^{n-1}v^{j+1}b_j\mathbf{1}_{\{k=j\}}
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death

namespace ActuarialAssurances

noncomputable def termPath (h n : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range n, if j < h then v^(j+1)*b j*death k j else 0
end ActuarialAssurances


