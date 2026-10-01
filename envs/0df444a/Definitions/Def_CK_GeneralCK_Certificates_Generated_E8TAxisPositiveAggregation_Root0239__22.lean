-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0239__22
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0239__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:38:46.35451+00:00
-- url     : https://prove2.me/theorems/b740d00f-9175-46db-a660-5a0d8502ea39
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0239 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0240, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0239 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0240, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0241, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0242, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0243, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0244, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0245, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0246, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0247, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0248, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0249, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0250, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0251, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0252, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0253, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0254, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0255, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0256, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0257, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0258, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0259, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0260)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0239 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0240, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0241, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0242, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0243, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0244, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0245, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0246, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0247, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0248, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0249, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0250, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0251, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0252, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0253, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0254, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0255, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0256, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0257, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0258, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0259, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0260)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0239 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0240, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0241, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0242, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0243, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0244, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0245, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0246, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0247, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0248, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0249, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0250, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0251, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0252, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0253, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0254, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0255, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0256, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0257, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0258, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0259, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0260) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0239 (+21 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0240, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0241, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0242, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0243, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0244, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0245, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0246, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0247, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0248, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0249, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0250, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0251, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0252, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0253, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0254, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0255, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0256, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0257, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0258, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0259, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0260).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0221Certified__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0240Certified__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0252Certified__19

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0239 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0239
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0239Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0239Geometry.rectangle, E8TAxisProd0239Geometry.sLower, E8TAxisProd0239Geometry.sUpper, E8TAxisProd0239Geometry.tLower, E8TAxisProd0239Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0239

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0240 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0240
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0240Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0240Geometry.rectangle, E8TAxisProd0240Geometry.sLower, E8TAxisProd0240Geometry.sUpper, E8TAxisProd0240Geometry.tLower, E8TAxisProd0240Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0240

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0241 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0241
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0241Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0241Geometry.rectangle, E8TAxisProd0241Geometry.sLower, E8TAxisProd0241Geometry.sUpper, E8TAxisProd0241Geometry.tLower, E8TAxisProd0241Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0241

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0242 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0242
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0242Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0242Geometry.rectangle, E8TAxisProd0242Geometry.sLower, E8TAxisProd0242Geometry.sUpper, E8TAxisProd0242Geometry.tLower, E8TAxisProd0242Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0242

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0243 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0243
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0243Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0243Geometry.rectangle, E8TAxisProd0243Geometry.sLower, E8TAxisProd0243Geometry.sUpper, E8TAxisProd0243Geometry.tLower, E8TAxisProd0243Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0243

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0244 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0244
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0244Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0244Geometry.rectangle, E8TAxisProd0244Geometry.sLower, E8TAxisProd0244Geometry.sUpper, E8TAxisProd0244Geometry.tLower, E8TAxisProd0244Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0244

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0245 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0245
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0245Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0245Geometry.rectangle, E8TAxisProd0245Geometry.sLower, E8TAxisProd0245Geometry.sUpper, E8TAxisProd0245Geometry.tLower, E8TAxisProd0245Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0245

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0246 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0246
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0246Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0246Geometry.rectangle, E8TAxisProd0246Geometry.sLower, E8TAxisProd0246Geometry.sUpper, E8TAxisProd0246Geometry.tLower, E8TAxisProd0246Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0246

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0247 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0247
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0247Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0247Geometry.rectangle, E8TAxisProd0247Geometry.sLower, E8TAxisProd0247Geometry.sUpper, E8TAxisProd0247Geometry.tLower, E8TAxisProd0247Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0247

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0248 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0248
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0248Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0248Geometry.rectangle, E8TAxisProd0248Geometry.sLower, E8TAxisProd0248Geometry.sUpper, E8TAxisProd0248Geometry.tLower, E8TAxisProd0248Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0248

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0249 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0249
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0249Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0249Geometry.rectangle, E8TAxisProd0249Geometry.sLower, E8TAxisProd0249Geometry.sUpper, E8TAxisProd0249Geometry.tLower, E8TAxisProd0249Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0249

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0250 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0250
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0250Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0250Geometry.rectangle, E8TAxisProd0250Geometry.sLower, E8TAxisProd0250Geometry.sUpper, E8TAxisProd0250Geometry.tLower, E8TAxisProd0250Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0250

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0251 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0251
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0251Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0251Geometry.rectangle, E8TAxisProd0251Geometry.sLower, E8TAxisProd0251Geometry.sUpper, E8TAxisProd0251Geometry.tLower, E8TAxisProd0251Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0251

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0252 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0252
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0252Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0252Geometry.rectangle, E8TAxisProd0252Geometry.sLower, E8TAxisProd0252Geometry.sUpper, E8TAxisProd0252Geometry.tLower, E8TAxisProd0252Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0252

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0253 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0253
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0253Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0253Geometry.rectangle, E8TAxisProd0253Geometry.sLower, E8TAxisProd0253Geometry.sUpper, E8TAxisProd0253Geometry.tLower, E8TAxisProd0253Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0253

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0254 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0254
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0254Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0254Geometry.rectangle, E8TAxisProd0254Geometry.sLower, E8TAxisProd0254Geometry.sUpper, E8TAxisProd0254Geometry.tLower, E8TAxisProd0254Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0254

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0255 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0255
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0255Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0255Geometry.rectangle, E8TAxisProd0255Geometry.sLower, E8TAxisProd0255Geometry.sUpper, E8TAxisProd0255Geometry.tLower, E8TAxisProd0255Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0255

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0256 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0256
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0256Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0256Geometry.rectangle, E8TAxisProd0256Geometry.sLower, E8TAxisProd0256Geometry.sUpper, E8TAxisProd0256Geometry.tLower, E8TAxisProd0256Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0256

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0257 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0257
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0257Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0257Geometry.rectangle, E8TAxisProd0257Geometry.sLower, E8TAxisProd0257Geometry.sUpper, E8TAxisProd0257Geometry.tLower, E8TAxisProd0257Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0257

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0258 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0258
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0258Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0258Geometry.rectangle, E8TAxisProd0258Geometry.sLower, E8TAxisProd0258Geometry.sUpper, E8TAxisProd0258Geometry.tLower, E8TAxisProd0258Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0258

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0259 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0259
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0259Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0259Geometry.rectangle, E8TAxisProd0259Geometry.sLower, E8TAxisProd0259Geometry.sUpper, E8TAxisProd0259Geometry.tLower, E8TAxisProd0259Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0259

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0260 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0260
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0260Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0260Geometry.rectangle, E8TAxisProd0260Geometry.sLower, E8TAxisProd0260Geometry.sUpper, E8TAxisProd0260Geometry.tLower, E8TAxisProd0260Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0260

end


