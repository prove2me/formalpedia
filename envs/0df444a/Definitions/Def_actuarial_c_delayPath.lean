-- Prove2me | Definitions.Def_actuarial_c_delayPath
-- name    : actuarial_c_delayPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:27:37.162033+00:00
-- url     : https://prove2.me/theorems/0fba4a6a-f696-47ff-a5e7-ec86092ab5db
-- title:
--   Realised death benefit with an explicit nonnegative integer settlement delay
-- statement:
--   Realised death benefit with an explicit nonnegative integer settlement delay.
--
--   Mathematical relation:
--
--   $$
--   Z_r(k)=\sum_{j=0}^{h-1}v^{j+1+r}b_j\mathbf{1}_{\{k=j\}}
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death

namespace ActuarialAssurances

noncomputable def delayPath (h lag : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range h, v^(j+1+lag)*b j*death k j
end ActuarialAssurances


