-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0660__28
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0660__28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:41:46.774883+00:00
-- url     : https://prove2.me/theorems/edea9a83-0581-4dea-9e63-73b6272676f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0660 (+27 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0661, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0660 (+27 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0661, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0662, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0663, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0664, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0665, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0666, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0667, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0668, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0669, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0670, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0671, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0672, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0673, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0674, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0675, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0676, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0677, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0678, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0679, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0680, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0681, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0682, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0683, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0684, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0685, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0686, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0687)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0660 (+27 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0661, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0662, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0663, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0664, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0665, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0666, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0667, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0668, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0669, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0670, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0671, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0672, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0673, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0674, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0675, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0676, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0677, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0678, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0679, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0680, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0681, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0682, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0683, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0684, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0685, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0686, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0687)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0660 (+27 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0661, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0662, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0663, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0664, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0665, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0666, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0667, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0668, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0669, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0670, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0671, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0672, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0673, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0674, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0675, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0676, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0677, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0678, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0679, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0680, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0681, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0682, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0683, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0684, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0685, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0686, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0687) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0660 (+27 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0661, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0662, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0663, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0664, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0665, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0666, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0667, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0668, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0669, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0670, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0671, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0672, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0673, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0674, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0675, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0676, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0677, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0678, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0679, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0680, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0681, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0682, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0683, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0684, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0685, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0686, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0687).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0658Certified__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0677Certified__11

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0660 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0660
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0660Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0660Geometry.rectangle, E8TAxisProd0660Geometry.sLower, E8TAxisProd0660Geometry.sUpper, E8TAxisProd0660Geometry.tLower, E8TAxisProd0660Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0660

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0661 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0661
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0661Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0661Geometry.rectangle, E8TAxisProd0661Geometry.sLower, E8TAxisProd0661Geometry.sUpper, E8TAxisProd0661Geometry.tLower, E8TAxisProd0661Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0661

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0662 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0662
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0662Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0662Geometry.rectangle, E8TAxisProd0662Geometry.sLower, E8TAxisProd0662Geometry.sUpper, E8TAxisProd0662Geometry.tLower, E8TAxisProd0662Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0662

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0663 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0663
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0663Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0663Geometry.rectangle, E8TAxisProd0663Geometry.sLower, E8TAxisProd0663Geometry.sUpper, E8TAxisProd0663Geometry.tLower, E8TAxisProd0663Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0663

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0664 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0664
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0664Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0664Geometry.rectangle, E8TAxisProd0664Geometry.sLower, E8TAxisProd0664Geometry.sUpper, E8TAxisProd0664Geometry.tLower, E8TAxisProd0664Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0664

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0665 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0665
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0665Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0665Geometry.rectangle, E8TAxisProd0665Geometry.sLower, E8TAxisProd0665Geometry.sUpper, E8TAxisProd0665Geometry.tLower, E8TAxisProd0665Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0665

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0666 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0666
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0666Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0666Geometry.rectangle, E8TAxisProd0666Geometry.sLower, E8TAxisProd0666Geometry.sUpper, E8TAxisProd0666Geometry.tLower, E8TAxisProd0666Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0666

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0667 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0667
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0667Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0667Geometry.rectangle, E8TAxisProd0667Geometry.sLower, E8TAxisProd0667Geometry.sUpper, E8TAxisProd0667Geometry.tLower, E8TAxisProd0667Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0667

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0668 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0668
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0668Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0668Geometry.rectangle, E8TAxisProd0668Geometry.sLower, E8TAxisProd0668Geometry.sUpper, E8TAxisProd0668Geometry.tLower, E8TAxisProd0668Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0668

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0669 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0669
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0669Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0669Geometry.rectangle, E8TAxisProd0669Geometry.sLower, E8TAxisProd0669Geometry.sUpper, E8TAxisProd0669Geometry.tLower, E8TAxisProd0669Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0669

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0670 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0670
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0670Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0670Geometry.rectangle, E8TAxisProd0670Geometry.sLower, E8TAxisProd0670Geometry.sUpper, E8TAxisProd0670Geometry.tLower, E8TAxisProd0670Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0670

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0671 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0671
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0671Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0671Geometry.rectangle, E8TAxisProd0671Geometry.sLower, E8TAxisProd0671Geometry.sUpper, E8TAxisProd0671Geometry.tLower, E8TAxisProd0671Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0671

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0672 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0672
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0672Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0672Geometry.rectangle, E8TAxisProd0672Geometry.sLower, E8TAxisProd0672Geometry.sUpper, E8TAxisProd0672Geometry.tLower, E8TAxisProd0672Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0672

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0673 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0673
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0673Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0673Geometry.rectangle, E8TAxisProd0673Geometry.sLower, E8TAxisProd0673Geometry.sUpper, E8TAxisProd0673Geometry.tLower, E8TAxisProd0673Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0673

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0674 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0674
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0674Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0674Geometry.rectangle, E8TAxisProd0674Geometry.sLower, E8TAxisProd0674Geometry.sUpper, E8TAxisProd0674Geometry.tLower, E8TAxisProd0674Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0674

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0675 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0675
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0675Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0675Geometry.rectangle, E8TAxisProd0675Geometry.sLower, E8TAxisProd0675Geometry.sUpper, E8TAxisProd0675Geometry.tLower, E8TAxisProd0675Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0675

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0676 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0676
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0676Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0676Geometry.rectangle, E8TAxisProd0676Geometry.sLower, E8TAxisProd0676Geometry.sUpper, E8TAxisProd0676Geometry.tLower, E8TAxisProd0676Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0676

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0677 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0677
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0677Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0677Geometry.rectangle, E8TAxisProd0677Geometry.sLower, E8TAxisProd0677Geometry.sUpper, E8TAxisProd0677Geometry.tLower, E8TAxisProd0677Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0677

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0678 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0678
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0678Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0678Geometry.rectangle, E8TAxisProd0678Geometry.sLower, E8TAxisProd0678Geometry.sUpper, E8TAxisProd0678Geometry.tLower, E8TAxisProd0678Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0678

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0679 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0679
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0679Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0679Geometry.rectangle, E8TAxisProd0679Geometry.sLower, E8TAxisProd0679Geometry.sUpper, E8TAxisProd0679Geometry.tLower, E8TAxisProd0679Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0679

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0680 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0680
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0680Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0680Geometry.rectangle, E8TAxisProd0680Geometry.sLower, E8TAxisProd0680Geometry.sUpper, E8TAxisProd0680Geometry.tLower, E8TAxisProd0680Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0680

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0681 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0681
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0681Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0681Geometry.rectangle, E8TAxisProd0681Geometry.sLower, E8TAxisProd0681Geometry.sUpper, E8TAxisProd0681Geometry.tLower, E8TAxisProd0681Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0681

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0682 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0682
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0682Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0682Geometry.rectangle, E8TAxisProd0682Geometry.sLower, E8TAxisProd0682Geometry.sUpper, E8TAxisProd0682Geometry.tLower, E8TAxisProd0682Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0682

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0683 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0683
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0683Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0683Geometry.rectangle, E8TAxisProd0683Geometry.sLower, E8TAxisProd0683Geometry.sUpper, E8TAxisProd0683Geometry.tLower, E8TAxisProd0683Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0683

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0684 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0684
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0684Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0684Geometry.rectangle, E8TAxisProd0684Geometry.sLower, E8TAxisProd0684Geometry.sUpper, E8TAxisProd0684Geometry.tLower, E8TAxisProd0684Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0684

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0685 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0685
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0685Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0685Geometry.rectangle, E8TAxisProd0685Geometry.sLower, E8TAxisProd0685Geometry.sUpper, E8TAxisProd0685Geometry.tLower, E8TAxisProd0685Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0685

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0686 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0686
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0686Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0686Geometry.rectangle, E8TAxisProd0686Geometry.sLower, E8TAxisProd0686Geometry.sUpper, E8TAxisProd0686Geometry.tLower, E8TAxisProd0686Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0686

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0687 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0687
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0687Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0687Geometry.rectangle, E8TAxisProd0687Geometry.sLower, E8TAxisProd0687Geometry.sUpper, E8TAxisProd0687Geometry.tLower, E8TAxisProd0687Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0687

end


