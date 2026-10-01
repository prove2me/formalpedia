-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0307__19
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0307__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:41:56.651984+00:00
-- url     : https://prove2.me/theorems/9fad207b-3a9b-4f7a-a10f-d77049bb5043
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0307 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0308, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0307 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0308, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0309, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0310, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0311, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0312, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0313, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0314, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0315, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0316, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0317, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0318, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0319, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0320, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0321, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0322, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0323, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0324, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0325)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0307 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0308, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0309, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0310, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0311, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0312, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0313, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0314, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0315, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0316, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0317, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0318, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0319, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0320, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0321, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0322, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0323, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0324, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0325)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0307 (+18 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0308, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0309, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0310, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0311, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0312, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0313, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0314, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0315, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0316, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0317, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0318, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0319, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0320, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0321, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0322, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0323, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0324, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0325) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0307 (+18 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0308, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0309, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0310, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0311, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0312, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0313, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0314, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0315, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0316, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0317, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0318, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0319, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0320, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0321, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0322, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0323, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0324, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0325).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0296Certified__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0317Certified__21

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0307 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0307
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0307Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0307Geometry.rectangle, E8TAxisProd0307Geometry.sLower, E8TAxisProd0307Geometry.sUpper, E8TAxisProd0307Geometry.tLower, E8TAxisProd0307Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0307

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0308 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0308
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0308Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0308Geometry.rectangle, E8TAxisProd0308Geometry.sLower, E8TAxisProd0308Geometry.sUpper, E8TAxisProd0308Geometry.tLower, E8TAxisProd0308Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0308

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0309 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0309
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0309Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0309Geometry.rectangle, E8TAxisProd0309Geometry.sLower, E8TAxisProd0309Geometry.sUpper, E8TAxisProd0309Geometry.tLower, E8TAxisProd0309Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0309

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0310 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0310
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0310Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0310Geometry.rectangle, E8TAxisProd0310Geometry.sLower, E8TAxisProd0310Geometry.sUpper, E8TAxisProd0310Geometry.tLower, E8TAxisProd0310Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0310

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0311 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0311
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0311Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0311Geometry.rectangle, E8TAxisProd0311Geometry.sLower, E8TAxisProd0311Geometry.sUpper, E8TAxisProd0311Geometry.tLower, E8TAxisProd0311Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0311

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0312 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0312
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0312Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0312Geometry.rectangle, E8TAxisProd0312Geometry.sLower, E8TAxisProd0312Geometry.sUpper, E8TAxisProd0312Geometry.tLower, E8TAxisProd0312Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0312

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0313 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0313
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0313Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0313Geometry.rectangle, E8TAxisProd0313Geometry.sLower, E8TAxisProd0313Geometry.sUpper, E8TAxisProd0313Geometry.tLower, E8TAxisProd0313Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0313

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0314 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0314
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0314Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0314Geometry.rectangle, E8TAxisProd0314Geometry.sLower, E8TAxisProd0314Geometry.sUpper, E8TAxisProd0314Geometry.tLower, E8TAxisProd0314Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0314

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0315 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0315
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0315Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0315Geometry.rectangle, E8TAxisProd0315Geometry.sLower, E8TAxisProd0315Geometry.sUpper, E8TAxisProd0315Geometry.tLower, E8TAxisProd0315Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0315

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0316 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0316
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0316Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0316Geometry.rectangle, E8TAxisProd0316Geometry.sLower, E8TAxisProd0316Geometry.sUpper, E8TAxisProd0316Geometry.tLower, E8TAxisProd0316Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0316

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0317 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0317
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0317Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0317Geometry.rectangle, E8TAxisProd0317Geometry.sLower, E8TAxisProd0317Geometry.sUpper, E8TAxisProd0317Geometry.tLower, E8TAxisProd0317Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0317

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0318 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0318
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0318Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0318Geometry.rectangle, E8TAxisProd0318Geometry.sLower, E8TAxisProd0318Geometry.sUpper, E8TAxisProd0318Geometry.tLower, E8TAxisProd0318Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0318

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0319 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0319
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(87 / 32 : ℝ), (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0319Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0319Geometry.rectangle, E8TAxisProd0319Geometry.sLower, E8TAxisProd0319Geometry.sUpper, E8TAxisProd0319Geometry.tLower, E8TAxisProd0319Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0319

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0320 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0320
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0320Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0320Geometry.rectangle, E8TAxisProd0320Geometry.sLower, E8TAxisProd0320Geometry.sUpper, E8TAxisProd0320Geometry.tLower, E8TAxisProd0320Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0320

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0321 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0321
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0321Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0321Geometry.rectangle, E8TAxisProd0321Geometry.sLower, E8TAxisProd0321Geometry.sUpper, E8TAxisProd0321Geometry.tLower, E8TAxisProd0321Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0321

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0322 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0322
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87 / 32 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0322Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0322Geometry.rectangle, E8TAxisProd0322Geometry.sLower, E8TAxisProd0322Geometry.sUpper, E8TAxisProd0322Geometry.tLower, E8TAxisProd0322Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0322

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0323 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0323
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0323Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0323Geometry.rectangle, E8TAxisProd0323Geometry.sLower, E8TAxisProd0323Geometry.sUpper, E8TAxisProd0323Geometry.tLower, E8TAxisProd0323Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0323

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0324 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0324
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0324Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0324Geometry.rectangle, E8TAxisProd0324Geometry.sLower, E8TAxisProd0324Geometry.sUpper, E8TAxisProd0324Geometry.tLower, E8TAxisProd0324Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0324

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0325 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0325
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0325Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0325Geometry.rectangle, E8TAxisProd0325Geometry.sLower, E8TAxisProd0325Geometry.sUpper, E8TAxisProd0325Geometry.tLower, E8TAxisProd0325Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0325

end


