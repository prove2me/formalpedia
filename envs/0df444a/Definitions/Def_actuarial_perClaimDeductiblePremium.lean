-- Prove2me | Definitions.Def_actuarial_perClaimDeductiblePremium
-- name    : actuarial_perClaimDeductiblePremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:43:06.716288+00:00
-- url     : https://prove2.me/theorems/1b8c63da-e069-4f08-a80c-00f80918c84e
-- title:
--   Expected ceded cost after separate per-claim deductibles
-- statement:
--   This is an original derived actuarial definition, based on the aggregate treaty compared with per occurrence excess-of-loss. The finite loss model applies the deductible separately within every scenario before multiplying ceded amounts by their nonnegative scenario weights. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \Pi_{\mathrm{individual}}=\sum_{s=0}^B w_s C_{\mathrm{individual}}(s)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration actuarial_perClaimDeductiblePremium is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

noncomputable def perClaimDeductiblePremium
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (B + 1),
    ((perClaimDeductibleCeded (x s) n d : ℕ) : ℝ) * w s

end ActuarialValuation


