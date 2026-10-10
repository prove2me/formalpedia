-- Prove2me | Definitions.Def_actuarial_layerCededPayment
-- name    : actuarial_layerCededPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:05.4701+00:00
-- url     : https://prove2.me/theorems/ab8d92e0-b904-4dc2-bb10-71af70a74296
-- title:
--   Capped single-layer reinsurance payment
-- statement:
--   For a claim amount x, a reinsurance layer of width or limit L attaching at d reimburses the lesser of excess x−d positive part and the layer limit. It pays zero below attachment and cannot pay more than L.
--
--   **Mathematical statement**
--
--   $$
--   C_{d,L}(x)=\min((x-d)_+,L)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration actuarial_layerCededPayment is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

noncomputable def layerCededPayment (loss attachment limit : ℕ) : ℕ :=
  min (layerExcessLoss loss attachment) limit

end ActuarialValuation


