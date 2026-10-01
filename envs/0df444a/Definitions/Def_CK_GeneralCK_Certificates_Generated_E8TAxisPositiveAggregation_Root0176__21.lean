-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0176__21
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0176__21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:30:49.034145+00:00
-- url     : https://prove2.me/theorems/ef163e0f-d8a9-40a6-8a2a-d46241551d01
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0176 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0177, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0176 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0177, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0178, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0179, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0180, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0181, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0182, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0183, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0184, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0185, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0186, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0187, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0188, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0189, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0190, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0191, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0192, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0193, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0194, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0195, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0196)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0176 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0177, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0178, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0179, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0180, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0181, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0182, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0183, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0184, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0185, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0186, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0187, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0188, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0189, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0190, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0191, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0192, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0193, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0194, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0195, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0196)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0176 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0177, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0178, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0179, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0180, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0181, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0182, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0183, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0184, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0185, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0186, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0187, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0188, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0189, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0190, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0191, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0192, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0193, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0194, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0195, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0196) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0176 (+20 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0177, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0178, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0179, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0180, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0181, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0182, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0183, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0184, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0185, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0186, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0187, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0188, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0189, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0190, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0191, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0192, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0193, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0194, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0195, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0196).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171Certified__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0187Certified__14

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0176 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0176
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0176Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0176Geometry.rectangle, E8TAxisProd0176Geometry.sLower, E8TAxisProd0176Geometry.sUpper, E8TAxisProd0176Geometry.tLower, E8TAxisProd0176Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0176

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0177 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0177
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0177Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0177Geometry.rectangle, E8TAxisProd0177Geometry.sLower, E8TAxisProd0177Geometry.sUpper, E8TAxisProd0177Geometry.tLower, E8TAxisProd0177Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0177

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0178 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0178
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0178Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0178Geometry.rectangle, E8TAxisProd0178Geometry.sLower, E8TAxisProd0178Geometry.sUpper, E8TAxisProd0178Geometry.tLower, E8TAxisProd0178Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0178

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0179 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0179
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0179Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0179Geometry.rectangle, E8TAxisProd0179Geometry.sLower, E8TAxisProd0179Geometry.sUpper, E8TAxisProd0179Geometry.tLower, E8TAxisProd0179Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0179

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0180 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0180
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0180Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0180Geometry.rectangle, E8TAxisProd0180Geometry.sLower, E8TAxisProd0180Geometry.sUpper, E8TAxisProd0180Geometry.tLower, E8TAxisProd0180Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0180

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0181 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0181
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0181Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0181Geometry.rectangle, E8TAxisProd0181Geometry.sLower, E8TAxisProd0181Geometry.sUpper, E8TAxisProd0181Geometry.tLower, E8TAxisProd0181Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0181

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0182 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0182
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0182Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0182Geometry.rectangle, E8TAxisProd0182Geometry.sLower, E8TAxisProd0182Geometry.sUpper, E8TAxisProd0182Geometry.tLower, E8TAxisProd0182Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0182

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0183 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0183
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0183Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0183Geometry.rectangle, E8TAxisProd0183Geometry.sLower, E8TAxisProd0183Geometry.sUpper, E8TAxisProd0183Geometry.tLower, E8TAxisProd0183Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0183

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0184 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0184
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0184Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0184Geometry.rectangle, E8TAxisProd0184Geometry.sLower, E8TAxisProd0184Geometry.sUpper, E8TAxisProd0184Geometry.tLower, E8TAxisProd0184Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0184

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0185 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0185
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0185Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0185Geometry.rectangle, E8TAxisProd0185Geometry.sLower, E8TAxisProd0185Geometry.sUpper, E8TAxisProd0185Geometry.tLower, E8TAxisProd0185Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0185

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0186 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0186
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0186Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0186Geometry.rectangle, E8TAxisProd0186Geometry.sLower, E8TAxisProd0186Geometry.sUpper, E8TAxisProd0186Geometry.tLower, E8TAxisProd0186Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0186

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0187 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0187
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0187Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0187Geometry.rectangle, E8TAxisProd0187Geometry.sLower, E8TAxisProd0187Geometry.sUpper, E8TAxisProd0187Geometry.tLower, E8TAxisProd0187Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0187

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0188 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0188
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0188Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0188Geometry.rectangle, E8TAxisProd0188Geometry.sLower, E8TAxisProd0188Geometry.sUpper, E8TAxisProd0188Geometry.tLower, E8TAxisProd0188Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0188

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0189 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0189
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0189Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0189Geometry.rectangle, E8TAxisProd0189Geometry.sLower, E8TAxisProd0189Geometry.sUpper, E8TAxisProd0189Geometry.tLower, E8TAxisProd0189Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0189

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0190 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0190
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0190Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0190Geometry.rectangle, E8TAxisProd0190Geometry.sLower, E8TAxisProd0190Geometry.sUpper, E8TAxisProd0190Geometry.tLower, E8TAxisProd0190Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0190

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0191 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0191
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0191Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0191Geometry.rectangle, E8TAxisProd0191Geometry.sLower, E8TAxisProd0191Geometry.sUpper, E8TAxisProd0191Geometry.tLower, E8TAxisProd0191Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0191

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0192 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0192
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0192Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0192Geometry.rectangle, E8TAxisProd0192Geometry.sLower, E8TAxisProd0192Geometry.sUpper, E8TAxisProd0192Geometry.tLower, E8TAxisProd0192Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0192

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0193 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0193
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0193Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0193Geometry.rectangle, E8TAxisProd0193Geometry.sLower, E8TAxisProd0193Geometry.sUpper, E8TAxisProd0193Geometry.tLower, E8TAxisProd0193Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0193

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0194 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0194
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0194Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0194Geometry.rectangle, E8TAxisProd0194Geometry.sLower, E8TAxisProd0194Geometry.sUpper, E8TAxisProd0194Geometry.tLower, E8TAxisProd0194Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0194

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0195 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0195
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0195Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0195Geometry.rectangle, E8TAxisProd0195Geometry.sLower, E8TAxisProd0195Geometry.sUpper, E8TAxisProd0195Geometry.tLower, E8TAxisProd0195Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0195

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0196 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0196
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0196Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0196Geometry.rectangle, E8TAxisProd0196Geometry.sLower, E8TAxisProd0196Geometry.sUpper, E8TAxisProd0196Geometry.tLower, E8TAxisProd0196Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0196

end


