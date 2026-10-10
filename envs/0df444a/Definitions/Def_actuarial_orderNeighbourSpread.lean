-- Prove2me | Definitions.Def_actuarial_orderNeighbourSpread
-- name    : actuarial_orderNeighbourSpread
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:24:09.417777+00:00
-- url     : https://prove2.me/theorems/0661139a-39b7-488d-9251-f2c47b118183
-- title:
--   Mean-preserving symmetric transfer from one claim amount to adjacent values
-- statement:
--   A fixed amount δ of probability mass is moved away from an interior integer claim level centre: half is allocated one unit below, and half one unit above. Under 1≤centre and centre+1≤B these three loss levels lie within the support and the transfer preserves the aggregate mean.
--
--   **Mathematical statement**
--
--   $$
--   w'_{c-1}=w_{c-1}+\delta/2,\ w'_c=w_c-\delta,\ w'_{c+1}=w_{c+1}+\delta/2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration actuarial_orderNeighbourSpread is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def orderNeighbourSpread
  (w : ℕ → ℝ) (centre : ℕ) (delta : ℝ) (s : ℕ) : ℝ :=
  w s +
    (if s + 1 = centre then delta / 2 else 0) +
    (if s = centre + 1 then delta / 2 else 0) -
    (if s = centre then delta else 0)

end ActuarialValuation


