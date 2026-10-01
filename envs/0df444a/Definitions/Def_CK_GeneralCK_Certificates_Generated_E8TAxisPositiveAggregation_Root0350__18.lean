-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0350__18
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0350__18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:52:17.632395+00:00
-- url     : https://prove2.me/theorems/ca9e4e55-94da-436b-8597-5d3d3388cff7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0350 (+17 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0351, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0350 (+17 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0351, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0352, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0353, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0354, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0355, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0356, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0357, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0358, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0359, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0360, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0361, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0362, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0363, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0364, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0365, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0366, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0367)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0350 (+17 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0351, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0352, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0353, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0354, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0355, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0356, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0357, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0358, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0359, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0360, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0361, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0362, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0363, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0364, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0365, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0366, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0367)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0350 (+17 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0351, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0352, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0353, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0354, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0355, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0356, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0357, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0358, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0359, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0360, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0361, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0362, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0363, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0364, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0365, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0366, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0367) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0350 (+17 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0351, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0352, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0353, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0354, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0355, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0356, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0357, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0358, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0359, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0360, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0361, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0362, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0363, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0364, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0365, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0366, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0367).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0338Certified__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357Certified__22

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0350 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0350
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0350Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0350Geometry.rectangle, E8TAxisProd0350Geometry.sLower, E8TAxisProd0350Geometry.sUpper, E8TAxisProd0350Geometry.tLower, E8TAxisProd0350Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0350

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0351 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0351
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0351Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0351Geometry.rectangle, E8TAxisProd0351Geometry.sLower, E8TAxisProd0351Geometry.sUpper, E8TAxisProd0351Geometry.tLower, E8TAxisProd0351Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0351

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0352 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0352
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0352Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0352Geometry.rectangle, E8TAxisProd0352Geometry.sLower, E8TAxisProd0352Geometry.sUpper, E8TAxisProd0352Geometry.tLower, E8TAxisProd0352Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0352

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0353 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0353
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0353Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0353Geometry.rectangle, E8TAxisProd0353Geometry.sLower, E8TAxisProd0353Geometry.sUpper, E8TAxisProd0353Geometry.tLower, E8TAxisProd0353Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0353

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0354 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0354
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0354Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0354Geometry.rectangle, E8TAxisProd0354Geometry.sLower, E8TAxisProd0354Geometry.sUpper, E8TAxisProd0354Geometry.tLower, E8TAxisProd0354Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0354

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0355 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0355
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0355Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0355Geometry.rectangle, E8TAxisProd0355Geometry.sLower, E8TAxisProd0355Geometry.sUpper, E8TAxisProd0355Geometry.tLower, E8TAxisProd0355Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0355

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0356 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0356
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0356Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0356Geometry.rectangle, E8TAxisProd0356Geometry.sLower, E8TAxisProd0356Geometry.sUpper, E8TAxisProd0356Geometry.tLower, E8TAxisProd0356Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0356

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0357 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0357
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0357Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0357Geometry.rectangle, E8TAxisProd0357Geometry.sLower, E8TAxisProd0357Geometry.sUpper, E8TAxisProd0357Geometry.tLower, E8TAxisProd0357Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0357

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0358 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0358
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0358Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0358Geometry.rectangle, E8TAxisProd0358Geometry.sLower, E8TAxisProd0358Geometry.sUpper, E8TAxisProd0358Geometry.tLower, E8TAxisProd0358Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0358

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0359 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0359
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0359Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0359Geometry.rectangle, E8TAxisProd0359Geometry.sLower, E8TAxisProd0359Geometry.sUpper, E8TAxisProd0359Geometry.tLower, E8TAxisProd0359Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0359

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0360 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0360
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0360Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0360Geometry.rectangle, E8TAxisProd0360Geometry.sLower, E8TAxisProd0360Geometry.sUpper, E8TAxisProd0360Geometry.tLower, E8TAxisProd0360Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0360

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0361 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0361
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0361Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0361Geometry.rectangle, E8TAxisProd0361Geometry.sLower, E8TAxisProd0361Geometry.sUpper, E8TAxisProd0361Geometry.tLower, E8TAxisProd0361Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0361

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0362 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0362
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0362Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0362Geometry.rectangle, E8TAxisProd0362Geometry.sLower, E8TAxisProd0362Geometry.sUpper, E8TAxisProd0362Geometry.tLower, E8TAxisProd0362Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0362

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0363 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0363
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0363Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0363Geometry.rectangle, E8TAxisProd0363Geometry.sLower, E8TAxisProd0363Geometry.sUpper, E8TAxisProd0363Geometry.tLower, E8TAxisProd0363Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0363

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0364 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0364
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0364Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0364Geometry.rectangle, E8TAxisProd0364Geometry.sLower, E8TAxisProd0364Geometry.sUpper, E8TAxisProd0364Geometry.tLower, E8TAxisProd0364Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0364

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0365 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0365
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0365Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0365Geometry.rectangle, E8TAxisProd0365Geometry.sLower, E8TAxisProd0365Geometry.sUpper, E8TAxisProd0365Geometry.tLower, E8TAxisProd0365Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0365

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0366 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0366
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0366Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0366Geometry.rectangle, E8TAxisProd0366Geometry.sLower, E8TAxisProd0366Geometry.sUpper, E8TAxisProd0366Geometry.tLower, E8TAxisProd0366Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0366

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0367 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0367
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0367Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0367Geometry.rectangle, E8TAxisProd0367Geometry.sLower, E8TAxisProd0367Geometry.sUpper, E8TAxisProd0367Geometry.tLower, E8TAxisProd0367Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0367

end


