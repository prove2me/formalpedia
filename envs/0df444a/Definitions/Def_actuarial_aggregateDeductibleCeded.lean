-- Prove2me | Definitions.Def_actuarial_aggregateDeductibleCeded
-- name    : actuarial_aggregateDeductibleCeded
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:42:19.593976+00:00
-- url     : https://prove2.me/theorems/e6fb08db-f1aa-487b-8f5c-843a9b814179
-- title:
--   Reinsurance ceded above one aggregate deductible
-- statement:
--   This is an original derived actuarial definition, based on the aggregate treaty compared with per occurrence excess-of-loss. An annual aggregate excess contract applies the single contractual deductible d to the gross sum of all covered claims. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{agg}}=(S_n-d)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration actuarial_aggregateDeductibleCeded is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal

namespace ActuarialValuation

noncomputable def aggregateDeductibleCeded (x : ℕ → ℕ) (n d : ℕ) : ℕ :=
  aggregateLossTotal x n - d

end ActuarialValuation


