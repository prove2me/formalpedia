-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0483__24
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0483__24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:06:32.942811+00:00
-- url     : https://prove2.me/theorems/2812b77e-b291-47ba-80f7-7a402be26130
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0483 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0484, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0483 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0484, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0485, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0486, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0487, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0488, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0489, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0490, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0491, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0492, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0493, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0494, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0495, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0496, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0497, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0498, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0499, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0500, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0501, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0502, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0503, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0504, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0505, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0506)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0483 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0484, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0485, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0486, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0487, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0488, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0489, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0490, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0491, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0492, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0493, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0494, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0495, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0496, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0497, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0498, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0499, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0500, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0501, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0502, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0503, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0504, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0505, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0506)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0483 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0484, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0485, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0486, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0487, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0488, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0489, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0490, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0491, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0492, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0493, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0494, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0495, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0496, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0497, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0498, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0499, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0500, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0501, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0502, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0503, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0504, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0505, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0506) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0483 (+23 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0484, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0485, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0486, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0487, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0488, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0489, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0490, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0491, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0492, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0493, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0494, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0495, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0496, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0497, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0498, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0499, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0500, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0501, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0502, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0503, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0504, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0505, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0506).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0473Certified__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0488Certified__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0505Certified__18

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0483 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0483
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0483Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0483Geometry.rectangle, E8TAxisProd0483Geometry.sLower, E8TAxisProd0483Geometry.sUpper, E8TAxisProd0483Geometry.tLower, E8TAxisProd0483Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0483

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0484 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0484
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0484Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0484Geometry.rectangle, E8TAxisProd0484Geometry.sLower, E8TAxisProd0484Geometry.sUpper, E8TAxisProd0484Geometry.tLower, E8TAxisProd0484Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0484

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0485 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0485
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0485Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0485Geometry.rectangle, E8TAxisProd0485Geometry.sLower, E8TAxisProd0485Geometry.sUpper, E8TAxisProd0485Geometry.tLower, E8TAxisProd0485Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0485

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0486 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0486
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0486Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0486Geometry.rectangle, E8TAxisProd0486Geometry.sLower, E8TAxisProd0486Geometry.sUpper, E8TAxisProd0486Geometry.tLower, E8TAxisProd0486Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0486

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0487 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0487
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0487Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0487Geometry.rectangle, E8TAxisProd0487Geometry.sLower, E8TAxisProd0487Geometry.sUpper, E8TAxisProd0487Geometry.tLower, E8TAxisProd0487Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0487

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0488 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0488
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0488Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0488Geometry.rectangle, E8TAxisProd0488Geometry.sLower, E8TAxisProd0488Geometry.sUpper, E8TAxisProd0488Geometry.tLower, E8TAxisProd0488Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0488

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0489 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0489
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0489Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0489Geometry.rectangle, E8TAxisProd0489Geometry.sLower, E8TAxisProd0489Geometry.sUpper, E8TAxisProd0489Geometry.tLower, E8TAxisProd0489Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0489

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0490 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0490
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0490Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0490Geometry.rectangle, E8TAxisProd0490Geometry.sLower, E8TAxisProd0490Geometry.sUpper, E8TAxisProd0490Geometry.tLower, E8TAxisProd0490Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0490

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0491 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0491
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0491Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0491Geometry.rectangle, E8TAxisProd0491Geometry.sLower, E8TAxisProd0491Geometry.sUpper, E8TAxisProd0491Geometry.tLower, E8TAxisProd0491Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0491

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0492 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0492
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0492Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0492Geometry.rectangle, E8TAxisProd0492Geometry.sLower, E8TAxisProd0492Geometry.sUpper, E8TAxisProd0492Geometry.tLower, E8TAxisProd0492Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0492

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0493 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0493
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0493Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0493Geometry.rectangle, E8TAxisProd0493Geometry.sLower, E8TAxisProd0493Geometry.sUpper, E8TAxisProd0493Geometry.tLower, E8TAxisProd0493Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0493

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0494 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0494
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0494Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0494Geometry.rectangle, E8TAxisProd0494Geometry.sLower, E8TAxisProd0494Geometry.sUpper, E8TAxisProd0494Geometry.tLower, E8TAxisProd0494Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0494

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0495 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0495
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0495Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0495Geometry.rectangle, E8TAxisProd0495Geometry.sLower, E8TAxisProd0495Geometry.sUpper, E8TAxisProd0495Geometry.tLower, E8TAxisProd0495Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0495

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0496 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0496
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0496Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0496Geometry.rectangle, E8TAxisProd0496Geometry.sLower, E8TAxisProd0496Geometry.sUpper, E8TAxisProd0496Geometry.tLower, E8TAxisProd0496Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0496

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0497 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0497
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0497Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0497Geometry.rectangle, E8TAxisProd0497Geometry.sLower, E8TAxisProd0497Geometry.sUpper, E8TAxisProd0497Geometry.tLower, E8TAxisProd0497Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0497

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0498 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0498
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0498Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0498Geometry.rectangle, E8TAxisProd0498Geometry.sLower, E8TAxisProd0498Geometry.sUpper, E8TAxisProd0498Geometry.tLower, E8TAxisProd0498Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0498

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0499 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0499
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0499Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0499Geometry.rectangle, E8TAxisProd0499Geometry.sLower, E8TAxisProd0499Geometry.sUpper, E8TAxisProd0499Geometry.tLower, E8TAxisProd0499Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0499

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0500 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0500
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0500Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0500Geometry.rectangle, E8TAxisProd0500Geometry.sLower, E8TAxisProd0500Geometry.sUpper, E8TAxisProd0500Geometry.tLower, E8TAxisProd0500Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0500

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0501 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0501
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0501Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0501Geometry.rectangle, E8TAxisProd0501Geometry.sLower, E8TAxisProd0501Geometry.sUpper, E8TAxisProd0501Geometry.tLower, E8TAxisProd0501Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0501

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0502 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0502
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0502Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0502Geometry.rectangle, E8TAxisProd0502Geometry.sLower, E8TAxisProd0502Geometry.sUpper, E8TAxisProd0502Geometry.tLower, E8TAxisProd0502Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0502

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0503 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0503
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0503Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0503Geometry.rectangle, E8TAxisProd0503Geometry.sLower, E8TAxisProd0503Geometry.sUpper, E8TAxisProd0503Geometry.tLower, E8TAxisProd0503Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0503

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0504 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0504
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0504Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0504Geometry.rectangle, E8TAxisProd0504Geometry.sLower, E8TAxisProd0504Geometry.sUpper, E8TAxisProd0504Geometry.tLower, E8TAxisProd0504Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0504

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0505 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0505
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0505Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0505Geometry.rectangle, E8TAxisProd0505Geometry.sLower, E8TAxisProd0505Geometry.sUpper, E8TAxisProd0505Geometry.tLower, E8TAxisProd0505Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0505

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0506 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0506
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0506Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0506Geometry.rectangle, E8TAxisProd0506Geometry.sLower, E8TAxisProd0506Geometry.sUpper, E8TAxisProd0506Geometry.tLower, E8TAxisProd0506Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0506

end


