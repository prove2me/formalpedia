-- Prove2me | Definitions.Def_ShipConsol_OneWH_Supplement_FixedRun
-- name    : ShipConsol_OneWH_Supplement_FixedRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:26:21.237985+00:00
-- url     : https://prove2.me/theorems/410503a7-abe9-4a69-83d2-80b09eef51c9
-- title:
--   Theorem 2 model, p. 14 — actual constant-threshold fixed-cost policy evaluation
-- statement:
--   For the fixed-cost one-warehouse model, absence is a distinct state and an active state records its minimum slack. With independent nonempty-arrival probability α, a constant-threshold policy ships all orders when z≤τ and holds otherwise, with forced terminal shipment. Shipping costs F(z); absence costs zero. After shipping or holding, arrival either adds slack d or leaves the retained minimum unchanged. Let J_T^τ(∅) be its recursively evaluated expected total cost from empty. Its expected average is
--
--   $$A_T^\tau=J_T^\tau(\varnothing)/T.$$
--
--   This is policy evaluation, not a new definition of the published Bellman optimum V. Any source batch law with the same nonempty probability yields this reduced fixed-cost process. The time until a nonempty arrival has support {1,2,…}; terminal arrivals incur no cost, as in DP (1).
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, §3, p. 10; Theorem 2, p. 14; proof OA2 (PDF34)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Control
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

namespace ShipConsol.OneWH.Supplement

/-- Policy evaluation only, not a redefinition of the published optimal DP. `none` is
absence. A nonempty batch contributes only its indicator in the fixed-cost model. -/
noncomputable def fixedPolicyTotal (F : ℝ → ℝ) (α : ℝ) (d τ : ℕ) :
    ℕ → Option ℕ → ℝ
  | 0, _ => 0
  | t + 1, s =>
    let ship := s.isSome ∧ (t = 0 ∨ s.getD 0 ≤ τ)
    let r := if ship then none else s.map (· - 1)
    (if ship then F (s.getD 0) else 0) +
      α * fixedPolicyTotal F α d τ t (some (min d (r.getD d))) +
      (1 - α) * fixedPolicyTotal F α d τ t r

/-- Mean cycle length is `1 / α + d - τ` for α>0. The no-arrival
value is explicitly its continuous cost extension zero. -/
noncomputable def fixedExpectedAverage (F : ℝ → ℝ) (α : ℝ) (d τ T : ℕ) : ℝ :=
  fixedPolicyTotal F α d τ T none / T

end ShipConsol.OneWH.Supplement


