-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0132__20
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0132__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:07:40.734462+00:00
-- url     : https://prove2.me/theorems/9b0962e4-977d-4084-becf-31ed7f35b24c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0132 (+19 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0133, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0132 (+19 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0133, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0134, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0135, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0136, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0137, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0138, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0139, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0140, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0141, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0142, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0143, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0144, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0145, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0146, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0147, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0148, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0149, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0150, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0151)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0132 (+19 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0133, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0134, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0135, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0136, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0137, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0138, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0139, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0140, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0141, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0142, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0143, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0144, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0145, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0146, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0147, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0148, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0149, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0150, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0151)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0132 (+19 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0133, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0134, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0135, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0136, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0137, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0138, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0139, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0140, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0141, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0142, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0143, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0144, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0145, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0146, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0147, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0148, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0149, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0150, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0151) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0132 (+19 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0133, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0134, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0135, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0136, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0137, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0138, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0139, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0140, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0141, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0142, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0143, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0144, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0145, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0146, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0147, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0148, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0149, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0150, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0151).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0118Certified__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0134Certified__23

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0132 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0132
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(29 / 16 : ℝ), (15 / 8 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0132Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0132Geometry.rectangle, E8TAxisProd0132Geometry.sLower, E8TAxisProd0132Geometry.sUpper, E8TAxisProd0132Geometry.tLower, E8TAxisProd0132Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0132

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0133 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0133
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 4 : ℝ), (29 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0133Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0133Geometry.rectangle, E8TAxisProd0133Geometry.sLower, E8TAxisProd0133Geometry.sUpper, E8TAxisProd0133Geometry.tLower, E8TAxisProd0133Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0133

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0134 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0134
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(29 / 16 : ℝ), (15 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0134Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0134Geometry.rectangle, E8TAxisProd0134Geometry.sLower, E8TAxisProd0134Geometry.sUpper, E8TAxisProd0134Geometry.tLower, E8TAxisProd0134Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0134

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0135 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0135
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 4 : ℝ), (29 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0135Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0135Geometry.rectangle, E8TAxisProd0135Geometry.sLower, E8TAxisProd0135Geometry.sUpper, E8TAxisProd0135Geometry.tLower, E8TAxisProd0135Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0135

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0136 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0136
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(31 / 16 : ℝ), (2 / 1 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0136Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0136Geometry.rectangle, E8TAxisProd0136Geometry.sLower, E8TAxisProd0136Geometry.sUpper, E8TAxisProd0136Geometry.tLower, E8TAxisProd0136Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0136

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0137 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0137
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15 / 8 : ℝ), (31 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0137Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0137Geometry.rectangle, E8TAxisProd0137Geometry.sLower, E8TAxisProd0137Geometry.sUpper, E8TAxisProd0137Geometry.tLower, E8TAxisProd0137Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0137

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0138 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0138
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(29 / 16 : ℝ), (15 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0138Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0138Geometry.rectangle, E8TAxisProd0138Geometry.sLower, E8TAxisProd0138Geometry.sUpper, E8TAxisProd0138Geometry.tLower, E8TAxisProd0138Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0138

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0139 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0139
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 4 : ℝ), (29 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0139Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0139Geometry.rectangle, E8TAxisProd0139Geometry.sLower, E8TAxisProd0139Geometry.sUpper, E8TAxisProd0139Geometry.tLower, E8TAxisProd0139Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0139

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0140 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0140
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0140Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0140Geometry.rectangle, E8TAxisProd0140Geometry.sLower, E8TAxisProd0140Geometry.sUpper, E8TAxisProd0140Geometry.tLower, E8TAxisProd0140Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0140

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0141 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0141
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0141Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0141Geometry.rectangle, E8TAxisProd0141Geometry.sLower, E8TAxisProd0141Geometry.sUpper, E8TAxisProd0141Geometry.tLower, E8TAxisProd0141Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0141

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0142 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0142
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0142Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0142Geometry.rectangle, E8TAxisProd0142Geometry.sLower, E8TAxisProd0142Geometry.sUpper, E8TAxisProd0142Geometry.tLower, E8TAxisProd0142Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0142

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0143 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0143
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0143Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0143Geometry.rectangle, E8TAxisProd0143Geometry.sLower, E8TAxisProd0143Geometry.sUpper, E8TAxisProd0143Geometry.tLower, E8TAxisProd0143Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0143

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0144 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0144
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0144Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0144Geometry.rectangle, E8TAxisProd0144Geometry.sLower, E8TAxisProd0144Geometry.sUpper, E8TAxisProd0144Geometry.tLower, E8TAxisProd0144Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0144

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0145 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0145
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0145Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0145Geometry.rectangle, E8TAxisProd0145Geometry.sLower, E8TAxisProd0145Geometry.sUpper, E8TAxisProd0145Geometry.tLower, E8TAxisProd0145Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0145

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0146 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0146
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0146Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0146Geometry.rectangle, E8TAxisProd0146Geometry.sLower, E8TAxisProd0146Geometry.sUpper, E8TAxisProd0146Geometry.tLower, E8TAxisProd0146Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0146

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0147 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0147
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0147Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0147Geometry.rectangle, E8TAxisProd0147Geometry.sLower, E8TAxisProd0147Geometry.sUpper, E8TAxisProd0147Geometry.tLower, E8TAxisProd0147Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0147

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0148 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0148
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0148Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0148Geometry.rectangle, E8TAxisProd0148Geometry.sLower, E8TAxisProd0148Geometry.sUpper, E8TAxisProd0148Geometry.tLower, E8TAxisProd0148Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0148

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0149 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0149
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0149Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0149Geometry.rectangle, E8TAxisProd0149Geometry.sLower, E8TAxisProd0149Geometry.sUpper, E8TAxisProd0149Geometry.tLower, E8TAxisProd0149Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0149

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0150 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0150
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0150Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0150Geometry.rectangle, E8TAxisProd0150Geometry.sLower, E8TAxisProd0150Geometry.sUpper, E8TAxisProd0150Geometry.tLower, E8TAxisProd0150Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0150

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0151 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0151
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0151Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0151Geometry.rectangle, E8TAxisProd0151Geometry.sLower, E8TAxisProd0151Geometry.sUpper, E8TAxisProd0151Geometry.tLower, E8TAxisProd0151Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0151

end


