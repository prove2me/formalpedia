-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0152__24
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0152__24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:15:30.886989+00:00
-- url     : https://prove2.me/theorems/5b1a49fc-9a60-47a0-835d-2b2c89a4c585
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0152 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0153, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0152 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0153, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0154, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0155, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0156, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0157, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0158, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0159, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0160, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0161, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0162, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0163, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0164, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0165, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0166, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0167, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0168, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0169, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0170, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0171, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0172, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0173, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0174, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0175)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0152 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0153, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0154, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0155, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0156, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0157, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0158, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0159, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0160, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0161, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0162, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0163, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0164, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0165, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0166, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0167, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0168, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0169, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0170, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0171, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0172, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0173, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0174, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0175)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0152 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0153, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0154, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0155, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0156, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0157, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0158, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0159, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0160, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0161, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0162, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0163, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0164, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0165, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0166, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0167, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0168, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0169, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0170, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0171, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0172, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0173, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0174, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0175) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0152 (+23 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0153, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0154, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0155, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0156, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0157, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0158, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0159, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0160, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0161, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0162, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0163, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0164, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0165, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0166, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0167, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0168, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0169, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0170, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0171, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0172, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0173, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0174, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0175).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0134Certified__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0157Certified__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0171Certified__16

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0152 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0152
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0152Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0152Geometry.rectangle, E8TAxisProd0152Geometry.sLower, E8TAxisProd0152Geometry.sUpper, E8TAxisProd0152Geometry.tLower, E8TAxisProd0152Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0152

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0153 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0153
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0153Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0153Geometry.rectangle, E8TAxisProd0153Geometry.sLower, E8TAxisProd0153Geometry.sUpper, E8TAxisProd0153Geometry.tLower, E8TAxisProd0153Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0153

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0154 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0154
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0154Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0154Geometry.rectangle, E8TAxisProd0154Geometry.sLower, E8TAxisProd0154Geometry.sUpper, E8TAxisProd0154Geometry.tLower, E8TAxisProd0154Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0154

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0155 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0155
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0155Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0155Geometry.rectangle, E8TAxisProd0155Geometry.sLower, E8TAxisProd0155Geometry.sUpper, E8TAxisProd0155Geometry.tLower, E8TAxisProd0155Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0155

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0156 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0156
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0156Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0156Geometry.rectangle, E8TAxisProd0156Geometry.sLower, E8TAxisProd0156Geometry.sUpper, E8TAxisProd0156Geometry.tLower, E8TAxisProd0156Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0156

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0157 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0157
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0157Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0157Geometry.rectangle, E8TAxisProd0157Geometry.sLower, E8TAxisProd0157Geometry.sUpper, E8TAxisProd0157Geometry.tLower, E8TAxisProd0157Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0157

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0158 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0158
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0158Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0158Geometry.rectangle, E8TAxisProd0158Geometry.sLower, E8TAxisProd0158Geometry.sUpper, E8TAxisProd0158Geometry.tLower, E8TAxisProd0158Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0158

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0159 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0159
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0159Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0159Geometry.rectangle, E8TAxisProd0159Geometry.sLower, E8TAxisProd0159Geometry.sUpper, E8TAxisProd0159Geometry.tLower, E8TAxisProd0159Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0159

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0160 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0160
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0160Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0160Geometry.rectangle, E8TAxisProd0160Geometry.sLower, E8TAxisProd0160Geometry.sUpper, E8TAxisProd0160Geometry.tLower, E8TAxisProd0160Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0160

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0161 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0161
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0161Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0161Geometry.rectangle, E8TAxisProd0161Geometry.sLower, E8TAxisProd0161Geometry.sUpper, E8TAxisProd0161Geometry.tLower, E8TAxisProd0161Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0161

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0162 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0162
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(23 / 16 : ℝ), (3 / 2 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0162Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0162Geometry.rectangle, E8TAxisProd0162Geometry.sLower, E8TAxisProd0162Geometry.sUpper, E8TAxisProd0162Geometry.tLower, E8TAxisProd0162Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0162

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0163 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0163
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 8 : ℝ), (23 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0163Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0163Geometry.rectangle, E8TAxisProd0163Geometry.sLower, E8TAxisProd0163Geometry.sUpper, E8TAxisProd0163Geometry.tLower, E8TAxisProd0163Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0163

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0164 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0164
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0164Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0164Geometry.rectangle, E8TAxisProd0164Geometry.sLower, E8TAxisProd0164Geometry.sUpper, E8TAxisProd0164Geometry.tLower, E8TAxisProd0164Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0164

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0165 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0165
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0165Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0165Geometry.rectangle, E8TAxisProd0165Geometry.sLower, E8TAxisProd0165Geometry.sUpper, E8TAxisProd0165Geometry.tLower, E8TAxisProd0165Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0165

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0166 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0166
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(21 / 16 : ℝ), (11 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0166Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0166Geometry.rectangle, E8TAxisProd0166Geometry.sLower, E8TAxisProd0166Geometry.sUpper, E8TAxisProd0166Geometry.tLower, E8TAxisProd0166Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0166

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0167 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0167
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 4 : ℝ), (21 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0167Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0167Geometry.rectangle, E8TAxisProd0167Geometry.sLower, E8TAxisProd0167Geometry.sUpper, E8TAxisProd0167Geometry.tLower, E8TAxisProd0167Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0167

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0168 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0168
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0168Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0168Geometry.rectangle, E8TAxisProd0168Geometry.sLower, E8TAxisProd0168Geometry.sUpper, E8TAxisProd0168Geometry.tLower, E8TAxisProd0168Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0168

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0169 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0169
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0169Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0169Geometry.rectangle, E8TAxisProd0169Geometry.sLower, E8TAxisProd0169Geometry.sUpper, E8TAxisProd0169Geometry.tLower, E8TAxisProd0169Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0169

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0170 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0170
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(19 / 16 : ℝ), (5 / 4 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0170Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0170Geometry.rectangle, E8TAxisProd0170Geometry.sLower, E8TAxisProd0170Geometry.sUpper, E8TAxisProd0170Geometry.tLower, E8TAxisProd0170Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0170

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0171 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0171
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 8 : ℝ), (19 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0171Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0171Geometry.rectangle, E8TAxisProd0171Geometry.sLower, E8TAxisProd0171Geometry.sUpper, E8TAxisProd0171Geometry.tLower, E8TAxisProd0171Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0171

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0172 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0172
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0172Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0172Geometry.rectangle, E8TAxisProd0172Geometry.sLower, E8TAxisProd0172Geometry.sUpper, E8TAxisProd0172Geometry.tLower, E8TAxisProd0172Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0172

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0173 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0173
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0173Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0173Geometry.rectangle, E8TAxisProd0173Geometry.sLower, E8TAxisProd0173Geometry.sUpper, E8TAxisProd0173Geometry.tLower, E8TAxisProd0173Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0173

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0174 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0174
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 16 : ℝ), (9 / 8 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0174Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0174Geometry.rectangle, E8TAxisProd0174Geometry.sLower, E8TAxisProd0174Geometry.sUpper, E8TAxisProd0174Geometry.tLower, E8TAxisProd0174Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0174

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0175 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0175
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 1 : ℝ), (17 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0175Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0175Geometry.rectangle, E8TAxisProd0175Geometry.sLower, E8TAxisProd0175Geometry.sUpper, E8TAxisProd0175Geometry.tLower, E8TAxisProd0175Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0175

end


