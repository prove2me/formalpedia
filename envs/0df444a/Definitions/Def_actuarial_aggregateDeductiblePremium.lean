-- Prove2me | Definitions.Def_actuarial_aggregateDeductiblePremium
-- name    : actuarial_aggregateDeductiblePremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:42:49.56998+00:00
-- url     : https://prove2.me/theorems/1fc9221a-676b-40a6-8d27-aff44178be62
-- title:
--   Expected ceded cost after aggregate deductible
-- statement:
--   This is an original derived actuarial definition, based on the aggregate treaty compared with per occurrence excess-of-loss. In a finite scenario table, scenario s has claim amounts x(s,i) and coefficient w(s); the net aggregate deductible premium is the expected aggregate ceded payment. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \Pi_{\mathrm{agg}}=\sum_{s=0}^B w_s C_{\mathrm{agg}}(s)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration actuarial_aggregateDeductiblePremium is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded

namespace ActuarialValuation

noncomputable def aggregateDeductiblePremium
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (B + 1),
    ((aggregateDeductibleCeded (x s) n d : ℕ) : ℝ) * w s

end ActuarialValuation


