-- Prove2me | Definitions.Def_actuarial_layerExpectedExcess
-- name    : actuarial_layerExpectedExcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:52.107975+00:00
-- url     : https://prove2.me/theorems/77d0fc58-1a5d-4c84-bf26-4a2a19857be6
-- title:
--   Finite unlimited stop-loss expected payment
-- statement:
--   The net stop-loss premium above an attachment d is the finite weighted expected excess claim amount without an upper layer cap. The difference of this value at d and at d+L will equal the capped layer's expected ceded cost.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{SL}(d)=\sum_{x=0}^{B}(x-d)_+w_x
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration actuarial_layerExpectedExcess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

noncomputable def layerExpectedExcess
  (w : ℕ → ℝ) (bound attachment : ℕ) : ℝ :=
  ∑ loss ∈ Finset.range (bound + 1),
    ((layerExcessLoss loss attachment : ℕ) : ℝ) * w loss

end ActuarialValuation


