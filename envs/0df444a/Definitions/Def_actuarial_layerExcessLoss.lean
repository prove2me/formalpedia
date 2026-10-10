-- Prove2me | Definitions.Def_actuarial_layerExcessLoss
-- name    : actuarial_layerExcessLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:28:47.946638+00:00
-- url     : https://prove2.me/theorems/10d1cb19-4786-4609-9f68-acdf7c2e69ae
-- title:
--   Single-claim positive excess over an attachment
-- statement:
--   The claim amount remaining above the insurer's retained attachment is natural-number positive-part subtraction. Below attachment it is zero, matching the gross excess payment of an unlimited stop-loss treaty.
--
--   **Mathematical statement**
--
--   $$
--   E_d(x)=(x-d)_+
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration actuarial_layerExcessLoss is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def layerExcessLoss (loss attachment : ℕ) : ℕ :=
  loss - attachment

end ActuarialValuation


