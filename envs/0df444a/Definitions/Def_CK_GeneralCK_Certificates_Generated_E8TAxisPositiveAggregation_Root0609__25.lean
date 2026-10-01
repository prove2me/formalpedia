-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0609__25
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0609__25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:49:27.27569+00:00
-- url     : https://prove2.me/theorems/f0e2b3bb-e49b-4a49-b505-dc0934cb6d5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0609 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0610, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0609 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0610, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0611, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0612, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0613, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0614, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0615, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0616, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0617, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0618, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0619, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0620, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0621, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0622, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0623, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0624, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0625, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0626, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0627, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0628, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0629, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0630, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0631, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0632, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0633)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0609 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0610, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0611, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0612, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0613, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0614, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0615, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0616, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0617, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0618, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0619, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0620, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0621, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0622, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0623, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0624, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0625, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0626, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0627, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0628, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0629, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0630, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0631, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0632, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0633)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0609 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0610, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0611, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0612, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0613, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0614, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0615, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0616, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0617, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0618, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0619, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0620, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0621, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0622, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0623, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0624, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0625, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0626, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0627, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0628, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0629, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0630, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0631, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0632, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0633) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0609 (+24 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0610, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0611, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0612, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0613, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0614, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0615, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0616, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0617, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0618, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0619, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0620, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0621, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0622, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0623, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0624, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0625, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0626, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0627, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0628, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0629, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0630, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0631, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0632, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0633).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0604Certified__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621Certified__21

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0609 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0609
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0609Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0609Geometry.rectangle, E8TAxisProd0609Geometry.sLower, E8TAxisProd0609Geometry.sUpper, E8TAxisProd0609Geometry.tLower, E8TAxisProd0609Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0609

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0610 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0610
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0610Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0610Geometry.rectangle, E8TAxisProd0610Geometry.sLower, E8TAxisProd0610Geometry.sUpper, E8TAxisProd0610Geometry.tLower, E8TAxisProd0610Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0610

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0611 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0611
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0611Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0611Geometry.rectangle, E8TAxisProd0611Geometry.sLower, E8TAxisProd0611Geometry.sUpper, E8TAxisProd0611Geometry.tLower, E8TAxisProd0611Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0611

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0612 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0612
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0612Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0612Geometry.rectangle, E8TAxisProd0612Geometry.sLower, E8TAxisProd0612Geometry.sUpper, E8TAxisProd0612Geometry.tLower, E8TAxisProd0612Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0612

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0613 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0613
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0613Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0613Geometry.rectangle, E8TAxisProd0613Geometry.sLower, E8TAxisProd0613Geometry.sUpper, E8TAxisProd0613Geometry.tLower, E8TAxisProd0613Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0613

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0614 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0614
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0614Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0614Geometry.rectangle, E8TAxisProd0614Geometry.sLower, E8TAxisProd0614Geometry.sUpper, E8TAxisProd0614Geometry.tLower, E8TAxisProd0614Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0614

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0615 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0615
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0615Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0615Geometry.rectangle, E8TAxisProd0615Geometry.sLower, E8TAxisProd0615Geometry.sUpper, E8TAxisProd0615Geometry.tLower, E8TAxisProd0615Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0615

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0616 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0616
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0616Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0616Geometry.rectangle, E8TAxisProd0616Geometry.sLower, E8TAxisProd0616Geometry.sUpper, E8TAxisProd0616Geometry.tLower, E8TAxisProd0616Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0616

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0617 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0617
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0617Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0617Geometry.rectangle, E8TAxisProd0617Geometry.sLower, E8TAxisProd0617Geometry.sUpper, E8TAxisProd0617Geometry.tLower, E8TAxisProd0617Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0617

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0618 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0618
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0618Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0618Geometry.rectangle, E8TAxisProd0618Geometry.sLower, E8TAxisProd0618Geometry.sUpper, E8TAxisProd0618Geometry.tLower, E8TAxisProd0618Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0618

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0619 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0619
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0619Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0619Geometry.rectangle, E8TAxisProd0619Geometry.sLower, E8TAxisProd0619Geometry.sUpper, E8TAxisProd0619Geometry.tLower, E8TAxisProd0619Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0619

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0620 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0620
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0620Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0620Geometry.rectangle, E8TAxisProd0620Geometry.sLower, E8TAxisProd0620Geometry.sUpper, E8TAxisProd0620Geometry.tLower, E8TAxisProd0620Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0620

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0621 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0621
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0621Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0621Geometry.rectangle, E8TAxisProd0621Geometry.sLower, E8TAxisProd0621Geometry.sUpper, E8TAxisProd0621Geometry.tLower, E8TAxisProd0621Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0621

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0622 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0622
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0622Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0622Geometry.rectangle, E8TAxisProd0622Geometry.sLower, E8TAxisProd0622Geometry.sUpper, E8TAxisProd0622Geometry.tLower, E8TAxisProd0622Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0622

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0623 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0623
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0623Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0623Geometry.rectangle, E8TAxisProd0623Geometry.sLower, E8TAxisProd0623Geometry.sUpper, E8TAxisProd0623Geometry.tLower, E8TAxisProd0623Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0623

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0624 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0624
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0624Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0624Geometry.rectangle, E8TAxisProd0624Geometry.sLower, E8TAxisProd0624Geometry.sUpper, E8TAxisProd0624Geometry.tLower, E8TAxisProd0624Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0624

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0625 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0625
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0625Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0625Geometry.rectangle, E8TAxisProd0625Geometry.sLower, E8TAxisProd0625Geometry.sUpper, E8TAxisProd0625Geometry.tLower, E8TAxisProd0625Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0625

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0626 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0626
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0626Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0626Geometry.rectangle, E8TAxisProd0626Geometry.sLower, E8TAxisProd0626Geometry.sUpper, E8TAxisProd0626Geometry.tLower, E8TAxisProd0626Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0626

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0627 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0627
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0627Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0627Geometry.rectangle, E8TAxisProd0627Geometry.sLower, E8TAxisProd0627Geometry.sUpper, E8TAxisProd0627Geometry.tLower, E8TAxisProd0627Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0627

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0628 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0628
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0628Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0628Geometry.rectangle, E8TAxisProd0628Geometry.sLower, E8TAxisProd0628Geometry.sUpper, E8TAxisProd0628Geometry.tLower, E8TAxisProd0628Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0628

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0629 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0629
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0629Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0629Geometry.rectangle, E8TAxisProd0629Geometry.sLower, E8TAxisProd0629Geometry.sUpper, E8TAxisProd0629Geometry.tLower, E8TAxisProd0629Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0629

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0630 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0630
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0630Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0630Geometry.rectangle, E8TAxisProd0630Geometry.sLower, E8TAxisProd0630Geometry.sUpper, E8TAxisProd0630Geometry.tLower, E8TAxisProd0630Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0630

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0631 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0631
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0631Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0631Geometry.rectangle, E8TAxisProd0631Geometry.sLower, E8TAxisProd0631Geometry.sUpper, E8TAxisProd0631Geometry.tLower, E8TAxisProd0631Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0631

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0632 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0632
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0632Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0632Geometry.rectangle, E8TAxisProd0632Geometry.sLower, E8TAxisProd0632Geometry.sUpper, E8TAxisProd0632Geometry.tLower, E8TAxisProd0632Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0632

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0633 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0633
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0633Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0633Geometry.rectangle, E8TAxisProd0633Geometry.sLower, E8TAxisProd0633Geometry.sUpper, E8TAxisProd0633Geometry.tLower, E8TAxisProd0633Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0633

end


