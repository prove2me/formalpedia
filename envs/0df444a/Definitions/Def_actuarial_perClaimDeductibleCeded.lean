-- Prove2me | Definitions.Def_actuarial_perClaimDeductibleCeded
-- name    : actuarial_perClaimDeductibleCeded
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:42:29.658394+00:00
-- url     : https://prove2.me/theorems/127142fe-7cbc-445f-afa9-998ee9c3c3e7
-- title:
--   Total ceded payments with a deductible on every claim
-- statement:
--   This is an original derived actuarial definition, based on the aggregate treaty compared with per occurrence excess-of-loss. An occurrence excess arrangement applies the full deductible separately to each claim and then sums all ceded claim amounts. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{individual}}=\sum_{i<n}(x_i-d)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration actuarial_perClaimDeductibleCeded is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def perClaimDeductibleCeded (x : ℕ → ℕ) (n d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (x i - d)

end ActuarialValuation


