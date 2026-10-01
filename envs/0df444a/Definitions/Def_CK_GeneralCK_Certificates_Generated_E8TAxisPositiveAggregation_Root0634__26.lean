-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0634__26
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0634__26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:18:14.764081+00:00
-- url     : https://prove2.me/theorems/2ade8a0a-0019-47df-bb19-abf0c7e0342f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0634 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0635, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0634 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0635, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0636, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0637, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0638, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0639, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0640, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0641, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0642, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0643, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0644, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0645, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0646, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0647, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0648, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0649, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0650, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0651, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0652, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0653, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0654, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0655, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0656, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0657, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0658, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0659)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0634 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0635, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0636, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0637, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0638, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0639, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0640, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0641, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0642, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0643, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0644, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0645, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0646, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0647, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0648, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0649, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0650, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0651, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0652, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0653, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0654, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0655, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0656, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0657, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0658, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0659)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0634 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0635, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0636, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0637, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0638, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0639, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0640, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0641, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0642, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0643, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0644, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0645, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0646, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0647, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0648, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0649, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0650, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0651, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0652, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0653, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0654, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0655, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0656, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0657, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0658, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0659) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0634 (+25 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0635, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0636, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0637, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0638, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0639, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0640, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0641, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0642, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0643, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0644, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0645, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0646, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0647, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0648, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0649, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0650, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0651, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0652, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0653, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0654, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0655, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0656, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0657, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0658, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0659).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621Certified__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0642Certified__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0658Certified__19

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0634 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0634
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0634Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0634Geometry.rectangle, E8TAxisProd0634Geometry.sLower, E8TAxisProd0634Geometry.sUpper, E8TAxisProd0634Geometry.tLower, E8TAxisProd0634Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0634

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0635 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0635
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0635Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0635Geometry.rectangle, E8TAxisProd0635Geometry.sLower, E8TAxisProd0635Geometry.sUpper, E8TAxisProd0635Geometry.tLower, E8TAxisProd0635Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0635

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0636 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0636
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0636Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0636Geometry.rectangle, E8TAxisProd0636Geometry.sLower, E8TAxisProd0636Geometry.sUpper, E8TAxisProd0636Geometry.tLower, E8TAxisProd0636Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0636

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0637 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0637
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0637Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0637Geometry.rectangle, E8TAxisProd0637Geometry.sLower, E8TAxisProd0637Geometry.sUpper, E8TAxisProd0637Geometry.tLower, E8TAxisProd0637Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0637

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0638 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0638
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0638Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0638Geometry.rectangle, E8TAxisProd0638Geometry.sLower, E8TAxisProd0638Geometry.sUpper, E8TAxisProd0638Geometry.tLower, E8TAxisProd0638Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0638

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0639 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0639
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0639Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0639Geometry.rectangle, E8TAxisProd0639Geometry.sLower, E8TAxisProd0639Geometry.sUpper, E8TAxisProd0639Geometry.tLower, E8TAxisProd0639Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0639

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0640 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0640
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0640Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0640Geometry.rectangle, E8TAxisProd0640Geometry.sLower, E8TAxisProd0640Geometry.sUpper, E8TAxisProd0640Geometry.tLower, E8TAxisProd0640Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0640

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0641 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0641
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0641Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0641Geometry.rectangle, E8TAxisProd0641Geometry.sLower, E8TAxisProd0641Geometry.sUpper, E8TAxisProd0641Geometry.tLower, E8TAxisProd0641Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0641

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0642 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0642
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0642Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0642Geometry.rectangle, E8TAxisProd0642Geometry.sLower, E8TAxisProd0642Geometry.sUpper, E8TAxisProd0642Geometry.tLower, E8TAxisProd0642Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0642

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0643 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0643
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0643Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0643Geometry.rectangle, E8TAxisProd0643Geometry.sLower, E8TAxisProd0643Geometry.sUpper, E8TAxisProd0643Geometry.tLower, E8TAxisProd0643Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0643

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0644 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0644
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0644Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0644Geometry.rectangle, E8TAxisProd0644Geometry.sLower, E8TAxisProd0644Geometry.sUpper, E8TAxisProd0644Geometry.tLower, E8TAxisProd0644Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0644

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0645 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0645
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0645Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0645Geometry.rectangle, E8TAxisProd0645Geometry.sLower, E8TAxisProd0645Geometry.sUpper, E8TAxisProd0645Geometry.tLower, E8TAxisProd0645Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0645

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0646 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0646
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0646Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0646Geometry.rectangle, E8TAxisProd0646Geometry.sLower, E8TAxisProd0646Geometry.sUpper, E8TAxisProd0646Geometry.tLower, E8TAxisProd0646Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0646

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0647 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0647
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0647Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0647Geometry.rectangle, E8TAxisProd0647Geometry.sLower, E8TAxisProd0647Geometry.sUpper, E8TAxisProd0647Geometry.tLower, E8TAxisProd0647Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0647

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0648 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0648
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0648Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0648Geometry.rectangle, E8TAxisProd0648Geometry.sLower, E8TAxisProd0648Geometry.sUpper, E8TAxisProd0648Geometry.tLower, E8TAxisProd0648Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0648

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0649 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0649
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0649Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0649Geometry.rectangle, E8TAxisProd0649Geometry.sLower, E8TAxisProd0649Geometry.sUpper, E8TAxisProd0649Geometry.tLower, E8TAxisProd0649Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0649

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0650 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0650
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0650Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0650Geometry.rectangle, E8TAxisProd0650Geometry.sLower, E8TAxisProd0650Geometry.sUpper, E8TAxisProd0650Geometry.tLower, E8TAxisProd0650Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0650

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0651 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0651
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0651Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0651Geometry.rectangle, E8TAxisProd0651Geometry.sLower, E8TAxisProd0651Geometry.sUpper, E8TAxisProd0651Geometry.tLower, E8TAxisProd0651Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0651

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0652 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0652
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0652Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0652Geometry.rectangle, E8TAxisProd0652Geometry.sLower, E8TAxisProd0652Geometry.sUpper, E8TAxisProd0652Geometry.tLower, E8TAxisProd0652Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0652

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0653 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0653
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0653Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0653Geometry.rectangle, E8TAxisProd0653Geometry.sLower, E8TAxisProd0653Geometry.sUpper, E8TAxisProd0653Geometry.tLower, E8TAxisProd0653Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0653

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0654 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0654
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0654Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0654Geometry.rectangle, E8TAxisProd0654Geometry.sLower, E8TAxisProd0654Geometry.sUpper, E8TAxisProd0654Geometry.tLower, E8TAxisProd0654Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0654

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0655 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0655
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0655Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0655Geometry.rectangle, E8TAxisProd0655Geometry.sLower, E8TAxisProd0655Geometry.sUpper, E8TAxisProd0655Geometry.tLower, E8TAxisProd0655Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0655

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0656 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0656
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0656Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0656Geometry.rectangle, E8TAxisProd0656Geometry.sLower, E8TAxisProd0656Geometry.sUpper, E8TAxisProd0656Geometry.tLower, E8TAxisProd0656Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0656

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0657 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0657
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0657Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0657Geometry.rectangle, E8TAxisProd0657Geometry.sLower, E8TAxisProd0657Geometry.sUpper, E8TAxisProd0657Geometry.tLower, E8TAxisProd0657Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0657

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0658 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0658
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0658Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0658Geometry.rectangle, E8TAxisProd0658Geometry.sLower, E8TAxisProd0658Geometry.sUpper, E8TAxisProd0658Geometry.tLower, E8TAxisProd0658Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0658

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0659 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0659
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0659Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0659Geometry.rectangle, E8TAxisProd0659Geometry.sLower, E8TAxisProd0659Geometry.sUpper, E8TAxisProd0659Geometry.tLower, E8TAxisProd0659Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0659

end


