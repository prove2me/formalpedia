-- Prove2me | Definitions.Def_Yukon_1a73be96c34fef79c5d93dc9
-- name    : Yukon_1a73be96c34fef79c5d93dc9
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:19:31.675623+00:00
-- url     : https://prove2.me/theorems/e2dc9c85-927f-4c71-90d4-2ff0b528ee6f
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ActualFirstCutPole6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ActualFirstCutPole6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ActualFirstCutPole6807.lean
--
--   yukon-proof-operation:foundation-direct-66fcd59399bdfc6f6c7a85d65674b85882f191a44f4b85cb58aa0df3ec75345c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDljNDkzNjg4NTdkNjU2NGNkZWI2YTdiMjkyZWI5YTM0N2Q3YjAzYWZiMDhiMTEzMTk3OWQyMmZiMDFjYjU4MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTY2ZmNkNTkzOTliZGZjNmY2YzdhODVkNjU2NzRiODU4ODJmMTkxYTQ0ZjRiODVjYjU4YWEwZGYzZWM3NTM0NWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xYTczYmU5NmMzNGZlZjc5YzVkOTNkYzkiLCJ2IjoyfQ]

/-
UNCOMPILED. Actual refined-coefficient interface for the first rational cut.
Copy FirstCutValuation6807.lean into ProximityPrize/SubmissionLower/ first.
This theorem has no first-tail-zero premise and does not manufacture a graph.
-/
import Definitions.Def_Yukon_553273187de1434da3936a72

import Definitions.Def_Yukon_043883ce6ed32260483e0ffb











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ActualFirstCutPole6807
open scoped BigOperators
open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open BoundaryTailAlgebra FirstCutValuation6807
set_option autoImplicit false
noncomputable section
variable {K Ω L : Type} [Field K] [Field Ω] [Field L]

/-- Includes zero-valued terms: logarithms are not applied as if they were units. -/
theorem pole_le_of_value_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (a : L) (bound : ℤ) (hb : 0 ≤ bound)
    (ha : V a ≤ WithZero.exp bound) : RCN187.poleOrder V a ≤ bound := by
  unfold RCN187.poleOrder
  apply max_le hb
  by_cases hz : V a = 0
  · simpa [hz] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr ha

end
end ProximityPrize.SubmissionLower.ActualFirstCutPole6807


