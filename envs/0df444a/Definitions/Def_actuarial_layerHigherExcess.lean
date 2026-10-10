-- Prove2me | Definitions.Def_actuarial_layerHigherExcess
-- name    : actuarial_layerHigherExcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:17.747188+00:00
-- url     : https://prove2.me/theorems/8a7603c7-03cb-427d-a5e3-729cebaf00e9
-- title:
--   Remaining gross excess above the top of the layer
-- statement:
--   Any part of the claim above the layer's upper attachment d+L is left for higher reinsurance layers or the ultimate insurer. It is the positive excess loss above the sum of the lower attachment and the stated layer width.
--
--   **Mathematical statement**
--
--   $$
--   H_{d,L}(x)=(x-d-L)_+
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration actuarial_layerHigherExcess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

noncomputable def layerHigherExcess (loss attachment limit : ℕ) : ℕ :=
  layerExcessLoss loss (attachment + limit)

end ActuarialValuation


