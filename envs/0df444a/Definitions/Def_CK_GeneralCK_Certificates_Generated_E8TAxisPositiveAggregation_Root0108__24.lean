-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0108__24
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0108__24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:09:21.498874+00:00
-- url     : https://prove2.me/theorems/bafc30ae-6090-44a2-8f06-c64987a875db
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0108 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0109, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0108 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0109, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0110, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0111, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0112, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0113, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0114, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0115, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0116, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0117, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0118, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0119, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0120, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0121, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0122, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0123, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0124, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0125, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0126, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0127, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0128, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0129, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0130, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0131)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0108 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0109, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0110, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0111, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0112, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0113, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0114, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0115, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0116, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0117, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0118, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0119, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0120, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0121, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0122, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0123, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0124, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0125, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0126, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0127, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0128, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0129, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0130, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0131)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0108 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0109, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0110, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0111, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0112, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0113, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0114, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0115, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0116, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0117, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0118, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0119, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0120, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0121, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0122, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0123, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0124, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0125, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0126, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0127, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0128, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0129, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0130, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0131) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0108 (+23 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0109, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0110, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0111, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0112, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0113, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0114, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0115, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0116, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0117, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0118, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0119, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0120, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0121, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0122, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0123, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0124, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0125, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0126, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0127, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0128, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0129, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0130, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0131).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0094Certified__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0118Certified__16

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0108 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0108
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(29 / 16 : ℝ), (15 / 8 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0108Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0108Geometry.rectangle, E8TAxisProd0108Geometry.sLower, E8TAxisProd0108Geometry.sUpper, E8TAxisProd0108Geometry.tLower, E8TAxisProd0108Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0108

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0109 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0109
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 4 : ℝ), (29 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0109Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0109Geometry.rectangle, E8TAxisProd0109Geometry.sLower, E8TAxisProd0109Geometry.sUpper, E8TAxisProd0109Geometry.tLower, E8TAxisProd0109Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0109

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0110 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0110
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(29 / 16 : ℝ), (15 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0110Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0110Geometry.rectangle, E8TAxisProd0110Geometry.sLower, E8TAxisProd0110Geometry.sUpper, E8TAxisProd0110Geometry.tLower, E8TAxisProd0110Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0110

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0111 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0111
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 4 : ℝ), (29 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0111Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0111Geometry.rectangle, E8TAxisProd0111Geometry.sLower, E8TAxisProd0111Geometry.sUpper, E8TAxisProd0111Geometry.tLower, E8TAxisProd0111Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0111

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0112 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0112
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0112Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0112Geometry.rectangle, E8TAxisProd0112Geometry.sLower, E8TAxisProd0112Geometry.sUpper, E8TAxisProd0112Geometry.tLower, E8TAxisProd0112Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0112

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0113 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0113
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0113Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0113Geometry.rectangle, E8TAxisProd0113Geometry.sLower, E8TAxisProd0113Geometry.sUpper, E8TAxisProd0113Geometry.tLower, E8TAxisProd0113Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0113

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0114 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0114
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0114Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0114Geometry.rectangle, E8TAxisProd0114Geometry.sLower, E8TAxisProd0114Geometry.sUpper, E8TAxisProd0114Geometry.tLower, E8TAxisProd0114Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0114

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0115 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0115
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0115Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0115Geometry.rectangle, E8TAxisProd0115Geometry.sLower, E8TAxisProd0115Geometry.sUpper, E8TAxisProd0115Geometry.tLower, E8TAxisProd0115Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0115

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0116 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0116
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0116Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0116Geometry.rectangle, E8TAxisProd0116Geometry.sLower, E8TAxisProd0116Geometry.sUpper, E8TAxisProd0116Geometry.tLower, E8TAxisProd0116Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0116

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0117 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0117
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0117Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0117Geometry.rectangle, E8TAxisProd0117Geometry.sLower, E8TAxisProd0117Geometry.sUpper, E8TAxisProd0117Geometry.tLower, E8TAxisProd0117Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0117

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0118 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0118
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0118Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0118Geometry.rectangle, E8TAxisProd0118Geometry.sLower, E8TAxisProd0118Geometry.sUpper, E8TAxisProd0118Geometry.tLower, E8TAxisProd0118Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0118

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0119 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0119
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0119Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0119Geometry.rectangle, E8TAxisProd0119Geometry.sLower, E8TAxisProd0119Geometry.sUpper, E8TAxisProd0119Geometry.tLower, E8TAxisProd0119Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0119

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0120 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0120
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0120Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0120Geometry.rectangle, E8TAxisProd0120Geometry.sLower, E8TAxisProd0120Geometry.sUpper, E8TAxisProd0120Geometry.tLower, E8TAxisProd0120Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0120

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0121 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0121
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0121Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0121Geometry.rectangle, E8TAxisProd0121Geometry.sLower, E8TAxisProd0121Geometry.sUpper, E8TAxisProd0121Geometry.tLower, E8TAxisProd0121Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0121

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0122 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0122
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(27 / 16 : ℝ), (7 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0122Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0122Geometry.rectangle, E8TAxisProd0122Geometry.sLower, E8TAxisProd0122Geometry.sUpper, E8TAxisProd0122Geometry.tLower, E8TAxisProd0122Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0122

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0123 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0123
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 8 : ℝ), (27 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0123Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0123Geometry.rectangle, E8TAxisProd0123Geometry.sLower, E8TAxisProd0123Geometry.sUpper, E8TAxisProd0123Geometry.tLower, E8TAxisProd0123Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0123

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0124 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0124
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0124Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0124Geometry.rectangle, E8TAxisProd0124Geometry.sLower, E8TAxisProd0124Geometry.sUpper, E8TAxisProd0124Geometry.tLower, E8TAxisProd0124Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0124

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0125 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0125
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0125Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0125Geometry.rectangle, E8TAxisProd0125Geometry.sLower, E8TAxisProd0125Geometry.sUpper, E8TAxisProd0125Geometry.tLower, E8TAxisProd0125Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0125

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0126 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0126
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(25 / 16 : ℝ), (13 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0126Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0126Geometry.rectangle, E8TAxisProd0126Geometry.sLower, E8TAxisProd0126Geometry.sUpper, E8TAxisProd0126Geometry.tLower, E8TAxisProd0126Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0126

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0127 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0127
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 2 : ℝ), (25 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0127Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0127Geometry.rectangle, E8TAxisProd0127Geometry.sLower, E8TAxisProd0127Geometry.sUpper, E8TAxisProd0127Geometry.tLower, E8TAxisProd0127Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0127

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0128 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0128
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(31 / 16 : ℝ), (2 / 1 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0128Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0128Geometry.rectangle, E8TAxisProd0128Geometry.sLower, E8TAxisProd0128Geometry.sUpper, E8TAxisProd0128Geometry.tLower, E8TAxisProd0128Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0128

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0129 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0129
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15 / 8 : ℝ), (31 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0129Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0129Geometry.rectangle, E8TAxisProd0129Geometry.sLower, E8TAxisProd0129Geometry.sUpper, E8TAxisProd0129Geometry.tLower, E8TAxisProd0129Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0129

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0130 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0130
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(31 / 16 : ℝ), (2 / 1 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0130Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0130Geometry.rectangle, E8TAxisProd0130Geometry.sLower, E8TAxisProd0130Geometry.sUpper, E8TAxisProd0130Geometry.tLower, E8TAxisProd0130Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0130

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0131 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0131
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15 / 8 : ℝ), (31 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0131Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0131Geometry.rectangle, E8TAxisProd0131Geometry.sLower, E8TAxisProd0131Geometry.sUpper, E8TAxisProd0131Geometry.tLower, E8TAxisProd0131Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0131

end


