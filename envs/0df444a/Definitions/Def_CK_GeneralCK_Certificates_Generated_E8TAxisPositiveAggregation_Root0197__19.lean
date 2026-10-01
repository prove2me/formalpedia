-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0197__19
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0197__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:44:05.022446+00:00
-- url     : https://prove2.me/theorems/abb0c24d-6ae2-42e5-a009-445f5aabcbdf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0197 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0198, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0197 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0198, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0199, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0200, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0201, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0202, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0203, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0204, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0205, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0206, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0207, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0208, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0209, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0210, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0211, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0212, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0213, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0214, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0215)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0197 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0198, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0199, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0200, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0201, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0202, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0203, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0204, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0205, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0206, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0207, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0208, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0209, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0210, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0211, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0212, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0213, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0214, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0215)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0197 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0198, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0199, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0200, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0201, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0202, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0203, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0204, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0205, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0206, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0207, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0208, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0209, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0210, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0211, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0212, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0213, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0214, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0215) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0197 (+18 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0198, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0199, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0200, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0201, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0202, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0203, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0204, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0205, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0206, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0207, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0208, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0209, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0210, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0211, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0212, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0213, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0214, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0215).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0187Certified__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Certified__20

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0197 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0197
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0197Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0197Geometry.rectangle, E8TAxisProd0197Geometry.sLower, E8TAxisProd0197Geometry.sUpper, E8TAxisProd0197Geometry.tLower, E8TAxisProd0197Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0197

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0198 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0198
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0198Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0198Geometry.rectangle, E8TAxisProd0198Geometry.sLower, E8TAxisProd0198Geometry.sUpper, E8TAxisProd0198Geometry.tLower, E8TAxisProd0198Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0198

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0199 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0199
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0199Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0199Geometry.rectangle, E8TAxisProd0199Geometry.sLower, E8TAxisProd0199Geometry.sUpper, E8TAxisProd0199Geometry.tLower, E8TAxisProd0199Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0199

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0200 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0200
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0200Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0200Geometry.rectangle, E8TAxisProd0200Geometry.sLower, E8TAxisProd0200Geometry.sUpper, E8TAxisProd0200Geometry.tLower, E8TAxisProd0200Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0200

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0201 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0201
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0201Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0201Geometry.rectangle, E8TAxisProd0201Geometry.sLower, E8TAxisProd0201Geometry.sUpper, E8TAxisProd0201Geometry.tLower, E8TAxisProd0201Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0201

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0202 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0202
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0202Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0202Geometry.rectangle, E8TAxisProd0202Geometry.sLower, E8TAxisProd0202Geometry.sUpper, E8TAxisProd0202Geometry.tLower, E8TAxisProd0202Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0202

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0203 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0203
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0203Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0203Geometry.rectangle, E8TAxisProd0203Geometry.sLower, E8TAxisProd0203Geometry.sUpper, E8TAxisProd0203Geometry.tLower, E8TAxisProd0203Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0203

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0204 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0204
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0204Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0204Geometry.rectangle, E8TAxisProd0204Geometry.sLower, E8TAxisProd0204Geometry.sUpper, E8TAxisProd0204Geometry.tLower, E8TAxisProd0204Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0204

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0205 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0205
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0205Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0205Geometry.rectangle, E8TAxisProd0205Geometry.sLower, E8TAxisProd0205Geometry.sUpper, E8TAxisProd0205Geometry.tLower, E8TAxisProd0205Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0205

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0206 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0206
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0206Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0206Geometry.rectangle, E8TAxisProd0206Geometry.sLower, E8TAxisProd0206Geometry.sUpper, E8TAxisProd0206Geometry.tLower, E8TAxisProd0206Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0206

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0207 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0207
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0207Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0207Geometry.rectangle, E8TAxisProd0207Geometry.sLower, E8TAxisProd0207Geometry.sUpper, E8TAxisProd0207Geometry.tLower, E8TAxisProd0207Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0207

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0208 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0208
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0208Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0208Geometry.rectangle, E8TAxisProd0208Geometry.sLower, E8TAxisProd0208Geometry.sUpper, E8TAxisProd0208Geometry.tLower, E8TAxisProd0208Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0208

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0209 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0209
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0209Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0209Geometry.rectangle, E8TAxisProd0209Geometry.sLower, E8TAxisProd0209Geometry.sUpper, E8TAxisProd0209Geometry.tLower, E8TAxisProd0209Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0209

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0210 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0210
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0210Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0210Geometry.rectangle, E8TAxisProd0210Geometry.sLower, E8TAxisProd0210Geometry.sUpper, E8TAxisProd0210Geometry.tLower, E8TAxisProd0210Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0210

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0211 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0211
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0211Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0211Geometry.rectangle, E8TAxisProd0211Geometry.sLower, E8TAxisProd0211Geometry.sUpper, E8TAxisProd0211Geometry.tLower, E8TAxisProd0211Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0211

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0212 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0212
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0212Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0212Geometry.rectangle, E8TAxisProd0212Geometry.sLower, E8TAxisProd0212Geometry.sUpper, E8TAxisProd0212Geometry.tLower, E8TAxisProd0212Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0212

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0213 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0213
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0213Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0213Geometry.rectangle, E8TAxisProd0213Geometry.sLower, E8TAxisProd0213Geometry.sUpper, E8TAxisProd0213Geometry.tLower, E8TAxisProd0213Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0213

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0214 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0214
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0214Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0214Geometry.rectangle, E8TAxisProd0214Geometry.sLower, E8TAxisProd0214Geometry.sUpper, E8TAxisProd0214Geometry.tLower, E8TAxisProd0214Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0214

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0215 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0215
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0215Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0215Geometry.rectangle, E8TAxisProd0215Geometry.sLower, E8TAxisProd0215Geometry.sUpper, E8TAxisProd0215Geometry.tLower, E8TAxisProd0215Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0215

end


