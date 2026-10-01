-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0285__22
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0285__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:47:53.81434+00:00
-- url     : https://prove2.me/theorems/30cc1bfc-130a-4155-924b-d9d34f02044b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0285 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0286, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0285 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0286, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0287, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0288, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0289, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0290, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0291, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0292, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0293, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0294, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0295, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0296, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0297, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0298, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0299, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0300, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0301, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0302, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0303, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0304, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0305, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0306)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0285 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0286, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0287, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0288, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0289, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0290, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0291, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0292, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0293, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0294, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0295, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0296, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0297, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0298, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0299, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0300, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0301, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0302, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0303, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0304, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0305, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0306)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0285 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0286, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0287, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0288, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0289, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0290, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0291, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0292, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0293, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0294, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0295, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0296, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0297, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0298, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0299, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0300, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0301, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0302, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0303, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0304, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0305, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0306) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0285 (+21 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0286, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0287, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0288, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0289, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0290, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0291, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0292, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0293, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0294, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0295, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0296, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0297, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0298, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0299, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0300, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0301, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0302, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0303, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0304, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0305, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0306).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0283Certified__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0296Certified__21

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0285 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0285
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0285Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0285Geometry.rectangle, E8TAxisProd0285Geometry.sLower, E8TAxisProd0285Geometry.sUpper, E8TAxisProd0285Geometry.tLower, E8TAxisProd0285Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0285

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0286 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0286
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0286Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0286Geometry.rectangle, E8TAxisProd0286Geometry.sLower, E8TAxisProd0286Geometry.sUpper, E8TAxisProd0286Geometry.tLower, E8TAxisProd0286Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0286

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0287 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0287
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0287Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0287Geometry.rectangle, E8TAxisProd0287Geometry.sLower, E8TAxisProd0287Geometry.sUpper, E8TAxisProd0287Geometry.tLower, E8TAxisProd0287Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0287

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0288 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0288
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0288Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0288Geometry.rectangle, E8TAxisProd0288Geometry.sLower, E8TAxisProd0288Geometry.sUpper, E8TAxisProd0288Geometry.tLower, E8TAxisProd0288Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0288

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0289 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0289
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0289Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0289Geometry.rectangle, E8TAxisProd0289Geometry.sLower, E8TAxisProd0289Geometry.sUpper, E8TAxisProd0289Geometry.tLower, E8TAxisProd0289Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0289

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0290 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0290
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0290Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0290Geometry.rectangle, E8TAxisProd0290Geometry.sLower, E8TAxisProd0290Geometry.sUpper, E8TAxisProd0290Geometry.tLower, E8TAxisProd0290Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0290

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0291 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0291
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0291Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0291Geometry.rectangle, E8TAxisProd0291Geometry.sLower, E8TAxisProd0291Geometry.sUpper, E8TAxisProd0291Geometry.tLower, E8TAxisProd0291Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0291

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0292 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0292
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0292Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0292Geometry.rectangle, E8TAxisProd0292Geometry.sLower, E8TAxisProd0292Geometry.sUpper, E8TAxisProd0292Geometry.tLower, E8TAxisProd0292Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0292

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0293 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0293
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0293Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0293Geometry.rectangle, E8TAxisProd0293Geometry.sLower, E8TAxisProd0293Geometry.sUpper, E8TAxisProd0293Geometry.tLower, E8TAxisProd0293Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0293

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0294 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0294
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0294Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0294Geometry.rectangle, E8TAxisProd0294Geometry.sLower, E8TAxisProd0294Geometry.sUpper, E8TAxisProd0294Geometry.tLower, E8TAxisProd0294Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0294

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0295 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0295
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0295Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0295Geometry.rectangle, E8TAxisProd0295Geometry.sLower, E8TAxisProd0295Geometry.sUpper, E8TAxisProd0295Geometry.tLower, E8TAxisProd0295Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0295

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0296 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0296
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0296Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0296Geometry.rectangle, E8TAxisProd0296Geometry.sLower, E8TAxisProd0296Geometry.sUpper, E8TAxisProd0296Geometry.tLower, E8TAxisProd0296Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0296

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0297 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0297
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0297Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0297Geometry.rectangle, E8TAxisProd0297Geometry.sLower, E8TAxisProd0297Geometry.sUpper, E8TAxisProd0297Geometry.tLower, E8TAxisProd0297Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0297

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0298 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0298
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0298Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0298Geometry.rectangle, E8TAxisProd0298Geometry.sLower, E8TAxisProd0298Geometry.sUpper, E8TAxisProd0298Geometry.tLower, E8TAxisProd0298Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0298

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0299 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0299
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0299Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0299Geometry.rectangle, E8TAxisProd0299Geometry.sLower, E8TAxisProd0299Geometry.sUpper, E8TAxisProd0299Geometry.tLower, E8TAxisProd0299Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0299

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0300 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0300
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0300Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0300Geometry.rectangle, E8TAxisProd0300Geometry.sLower, E8TAxisProd0300Geometry.sUpper, E8TAxisProd0300Geometry.tLower, E8TAxisProd0300Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0300

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0301 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0301
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0301Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0301Geometry.rectangle, E8TAxisProd0301Geometry.sLower, E8TAxisProd0301Geometry.sUpper, E8TAxisProd0301Geometry.tLower, E8TAxisProd0301Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0301

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0302 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0302
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0302Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0302Geometry.rectangle, E8TAxisProd0302Geometry.sLower, E8TAxisProd0302Geometry.sUpper, E8TAxisProd0302Geometry.tLower, E8TAxisProd0302Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0302

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0303 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0303
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0303Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0303Geometry.rectangle, E8TAxisProd0303Geometry.sLower, E8TAxisProd0303Geometry.sUpper, E8TAxisProd0303Geometry.tLower, E8TAxisProd0303Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0303

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0304 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0304
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0304Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0304Geometry.rectangle, E8TAxisProd0304Geometry.sLower, E8TAxisProd0304Geometry.sUpper, E8TAxisProd0304Geometry.tLower, E8TAxisProd0304Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0304

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0305 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0305
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0305Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0305Geometry.rectangle, E8TAxisProd0305Geometry.sLower, E8TAxisProd0305Geometry.sUpper, E8TAxisProd0305Geometry.tLower, E8TAxisProd0305Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0305

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0306 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0306
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0306Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0306Geometry.rectangle, E8TAxisProd0306Geometry.sLower, E8TAxisProd0306Geometry.sUpper, E8TAxisProd0306Geometry.tLower, E8TAxisProd0306Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0306

end


