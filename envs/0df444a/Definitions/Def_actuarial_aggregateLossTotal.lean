-- Prove2me | Definitions.Def_actuarial_aggregateLossTotal
-- name    : actuarial_aggregateLossTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:42:08.424149+00:00
-- url     : https://prove2.me/theorems/f6e8115d-c1bf-447e-a981-b76fac5812d4
-- title:
--   Portfolio gross claims in the treaty period
-- statement:
--   This is an original derived actuarial definition, based on the aggregate treaty compared with per occurrence excess-of-loss. The gross aggregate of the first n nonnegative integer-valued claims is computed before any annual aggregate attachment. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   S_n=\sum_{i=0}^{n-1}x_i
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration actuarial_aggregateLossTotal is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def aggregateLossTotal (x : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, x i

end ActuarialValuation


