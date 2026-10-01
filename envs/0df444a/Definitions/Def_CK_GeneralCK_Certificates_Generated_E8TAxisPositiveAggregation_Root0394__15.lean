-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0394__15
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0394__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:22:55.601591+00:00
-- url     : https://prove2.me/theorems/b78de32f-4f3f-465c-9fba-20f993c8bbd2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0394 (+14 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0395, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0394 (+14 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0395, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0396, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0397, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0398, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0399, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0400, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0401, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0402, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0403, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0404, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0405, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0406, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0407, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0408)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0394 (+14 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0395, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0396, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0397, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0398, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0399, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0400, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0401, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0402, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0403, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0404, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0405, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0406, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0407, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0408)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0394 (+14 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0395, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0396, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0397, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0398, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0399, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0400, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0401, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0402, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0403, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0404, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0405, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0406, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0407, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0408) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0394 (+14 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0395, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0396, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0397, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0398, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0399, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0400, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0401, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0402, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0403, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0404, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0405, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0406, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0407, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0408).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0379Certified__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0399Certified__17

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0394 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0394
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0394Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0394Geometry.rectangle, E8TAxisProd0394Geometry.sLower, E8TAxisProd0394Geometry.sUpper, E8TAxisProd0394Geometry.tLower, E8TAxisProd0394Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0394

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0395 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0395
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0395Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0395Geometry.rectangle, E8TAxisProd0395Geometry.sLower, E8TAxisProd0395Geometry.sUpper, E8TAxisProd0395Geometry.tLower, E8TAxisProd0395Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0395

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0396 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0396
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0396Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0396Geometry.rectangle, E8TAxisProd0396Geometry.sLower, E8TAxisProd0396Geometry.sUpper, E8TAxisProd0396Geometry.tLower, E8TAxisProd0396Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0396

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0397 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0397
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0397Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0397Geometry.rectangle, E8TAxisProd0397Geometry.sLower, E8TAxisProd0397Geometry.sUpper, E8TAxisProd0397Geometry.tLower, E8TAxisProd0397Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0397

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0398 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0398
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0398Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0398Geometry.rectangle, E8TAxisProd0398Geometry.sLower, E8TAxisProd0398Geometry.sUpper, E8TAxisProd0398Geometry.tLower, E8TAxisProd0398Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0398

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0399 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0399
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0399Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0399Geometry.rectangle, E8TAxisProd0399Geometry.sLower, E8TAxisProd0399Geometry.sUpper, E8TAxisProd0399Geometry.tLower, E8TAxisProd0399Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0399

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0400 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0400
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0400Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0400Geometry.rectangle, E8TAxisProd0400Geometry.sLower, E8TAxisProd0400Geometry.sUpper, E8TAxisProd0400Geometry.tLower, E8TAxisProd0400Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0400

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0401 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0401
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0401Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0401Geometry.rectangle, E8TAxisProd0401Geometry.sLower, E8TAxisProd0401Geometry.sUpper, E8TAxisProd0401Geometry.tLower, E8TAxisProd0401Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0401

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0402 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0402
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0402Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0402Geometry.rectangle, E8TAxisProd0402Geometry.sLower, E8TAxisProd0402Geometry.sUpper, E8TAxisProd0402Geometry.tLower, E8TAxisProd0402Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0402

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0403 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0403
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0403Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0403Geometry.rectangle, E8TAxisProd0403Geometry.sLower, E8TAxisProd0403Geometry.sUpper, E8TAxisProd0403Geometry.tLower, E8TAxisProd0403Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0403

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0404 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0404
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0404Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0404Geometry.rectangle, E8TAxisProd0404Geometry.sLower, E8TAxisProd0404Geometry.sUpper, E8TAxisProd0404Geometry.tLower, E8TAxisProd0404Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0404

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0405 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0405
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0405Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0405Geometry.rectangle, E8TAxisProd0405Geometry.sLower, E8TAxisProd0405Geometry.sUpper, E8TAxisProd0405Geometry.tLower, E8TAxisProd0405Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0405

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0406 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0406
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0406Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0406Geometry.rectangle, E8TAxisProd0406Geometry.sLower, E8TAxisProd0406Geometry.sUpper, E8TAxisProd0406Geometry.tLower, E8TAxisProd0406Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0406

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0407 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0407
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0407Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0407Geometry.rectangle, E8TAxisProd0407Geometry.sLower, E8TAxisProd0407Geometry.sUpper, E8TAxisProd0407Geometry.tLower, E8TAxisProd0407Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0407

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0408 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0408
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0408Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0408Geometry.rectangle, E8TAxisProd0408Geometry.sLower, E8TAxisProd0408Geometry.sUpper, E8TAxisProd0408Geometry.tLower, E8TAxisProd0408Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0408

end


