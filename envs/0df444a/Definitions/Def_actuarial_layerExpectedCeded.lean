-- Prove2me | Definitions.Def_actuarial_layerExpectedCeded
-- name    : actuarial_layerExpectedCeded
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:33.372087+00:00
-- url     : https://prove2.me/theorems/22e18729-f116-4619-b1e3-f87a3475234a
-- title:
--   Finite aggregate expected ceded loss cost of a layer
-- statement:
--   The finite bounded claim-severity mass model computes the net expected excess-of-loss reinsurance premium by weighting each loss payment of the capped layer by its claim probability. Expected ceded cost excludes risk loading and expenses.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{EL}_{d,L}=\sum_{x=0}^{B}C_{d,L}(x)w_x
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration actuarial_layerExpectedCeded is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

noncomputable def layerExpectedCeded
  (w : ℕ → ℝ) (bound attachment limit : ℕ) : ℝ :=
  ∑ loss ∈ Finset.range (bound + 1),
    ((layerCededPayment loss attachment limit : ℕ) : ℝ) * w loss

end ActuarialValuation


