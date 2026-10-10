-- Prove2me | Definitions.Def_actuarial_orderStopLossPremium
-- name    : actuarial_orderStopLossPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:23:42.340309+00:00
-- url     : https://prove2.me/theorems/6c3ab309-3701-487f-a605-01334247e3a1
-- title:
--   Bounded discrete expected excess above an integer attachment
-- statement:
--   The actuarial stop-loss transform multiplies each aggregate loss's excess over the attachment point by its real coefficient and sums over the finite covered loss grid. A nonnegative probability mass law gives its net excess-of-loss reinsurance premium.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_w(d)=\sum_{s=0}^{B}(s-d)_+w_s
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration actuarial_orderStopLossPremium is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def orderStopLossPremium
  (w : ℕ → ℝ) (bound deductible : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1),
    ((s - deductible : ℕ) : ℝ) * w s

end ActuarialValuation


