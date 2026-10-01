-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0216__23
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0216__23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:47:12.926837+00:00
-- url     : https://prove2.me/theorems/e5b21f74-be6e-4b62-836f-fc47b6f4cada
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0216 (+22 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0217, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0216 (+22 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0217, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0218, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0219, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0220, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0221, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0222, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0223, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0224, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0225, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0226, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0227, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0228, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0229, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0230, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0231, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0232, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0233, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0234, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0235, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0236, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0237, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0238)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0216 (+22 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0217, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0218, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0219, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0220, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0221, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0222, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0223, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0224, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0225, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0226, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0227, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0228, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0229, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0230, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0231, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0232, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0233, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0234, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0235, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0236, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0237, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0238)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0216 (+22 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0217, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0218, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0219, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0220, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0221, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0222, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0223, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0224, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0225, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0226, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0227, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0228, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0229, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0230, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0231, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0232, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0233, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0234, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0235, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0236, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0237, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0238) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0216 (+22 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0217, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0218, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0219, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0220, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0221, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0222, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0223, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0224, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0225, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0226, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0227, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0228, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0229, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0230, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0231, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0232, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0233, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0234, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0235, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0236, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0237, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0238).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Certified__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0221Certified__19

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0216 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0216
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0216Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0216Geometry.rectangle, E8TAxisProd0216Geometry.sLower, E8TAxisProd0216Geometry.sUpper, E8TAxisProd0216Geometry.tLower, E8TAxisProd0216Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0216

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0217 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0217
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0217Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0217Geometry.rectangle, E8TAxisProd0217Geometry.sLower, E8TAxisProd0217Geometry.sUpper, E8TAxisProd0217Geometry.tLower, E8TAxisProd0217Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0217

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0218 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0218
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0218Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0218Geometry.rectangle, E8TAxisProd0218Geometry.sLower, E8TAxisProd0218Geometry.sUpper, E8TAxisProd0218Geometry.tLower, E8TAxisProd0218Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0218

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0219 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0219
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0219Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0219Geometry.rectangle, E8TAxisProd0219Geometry.sLower, E8TAxisProd0219Geometry.sUpper, E8TAxisProd0219Geometry.tLower, E8TAxisProd0219Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0219

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0220 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0220
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0220Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0220Geometry.rectangle, E8TAxisProd0220Geometry.sLower, E8TAxisProd0220Geometry.sUpper, E8TAxisProd0220Geometry.tLower, E8TAxisProd0220Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0220

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0221 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0221
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0221Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0221Geometry.rectangle, E8TAxisProd0221Geometry.sLower, E8TAxisProd0221Geometry.sUpper, E8TAxisProd0221Geometry.tLower, E8TAxisProd0221Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0221

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0222 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0222
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0222Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0222Geometry.rectangle, E8TAxisProd0222Geometry.sLower, E8TAxisProd0222Geometry.sUpper, E8TAxisProd0222Geometry.tLower, E8TAxisProd0222Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0222

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0223 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0223
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0223Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0223Geometry.rectangle, E8TAxisProd0223Geometry.sLower, E8TAxisProd0223Geometry.sUpper, E8TAxisProd0223Geometry.tLower, E8TAxisProd0223Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0223

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0224 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0224
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0224Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0224Geometry.rectangle, E8TAxisProd0224Geometry.sLower, E8TAxisProd0224Geometry.sUpper, E8TAxisProd0224Geometry.tLower, E8TAxisProd0224Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0224

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0225 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0225
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0225Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0225Geometry.rectangle, E8TAxisProd0225Geometry.sLower, E8TAxisProd0225Geometry.sUpper, E8TAxisProd0225Geometry.tLower, E8TAxisProd0225Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0225

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0226 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0226
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0226Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0226Geometry.rectangle, E8TAxisProd0226Geometry.sLower, E8TAxisProd0226Geometry.sUpper, E8TAxisProd0226Geometry.tLower, E8TAxisProd0226Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0226

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0227 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0227
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0227Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0227Geometry.rectangle, E8TAxisProd0227Geometry.sLower, E8TAxisProd0227Geometry.sUpper, E8TAxisProd0227Geometry.tLower, E8TAxisProd0227Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0227

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0228 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0228
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0228Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0228Geometry.rectangle, E8TAxisProd0228Geometry.sLower, E8TAxisProd0228Geometry.sUpper, E8TAxisProd0228Geometry.tLower, E8TAxisProd0228Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0228

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0229 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0229
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0229Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0229Geometry.rectangle, E8TAxisProd0229Geometry.sLower, E8TAxisProd0229Geometry.sUpper, E8TAxisProd0229Geometry.tLower, E8TAxisProd0229Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0229

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0230 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0230
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0230Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0230Geometry.rectangle, E8TAxisProd0230Geometry.sLower, E8TAxisProd0230Geometry.sUpper, E8TAxisProd0230Geometry.tLower, E8TAxisProd0230Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0230

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0231 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0231
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0231Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0231Geometry.rectangle, E8TAxisProd0231Geometry.sLower, E8TAxisProd0231Geometry.sUpper, E8TAxisProd0231Geometry.tLower, E8TAxisProd0231Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0231

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0232 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0232
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0232Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0232Geometry.rectangle, E8TAxisProd0232Geometry.sLower, E8TAxisProd0232Geometry.sUpper, E8TAxisProd0232Geometry.tLower, E8TAxisProd0232Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0232

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0233 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0233
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0233Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0233Geometry.rectangle, E8TAxisProd0233Geometry.sLower, E8TAxisProd0233Geometry.sUpper, E8TAxisProd0233Geometry.tLower, E8TAxisProd0233Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0233

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0234 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0234
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0234Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0234Geometry.rectangle, E8TAxisProd0234Geometry.sLower, E8TAxisProd0234Geometry.sUpper, E8TAxisProd0234Geometry.tLower, E8TAxisProd0234Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0234

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0235 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0235
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0235Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0235Geometry.rectangle, E8TAxisProd0235Geometry.sLower, E8TAxisProd0235Geometry.sUpper, E8TAxisProd0235Geometry.tLower, E8TAxisProd0235Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0235

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0236 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0236
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0236Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0236Geometry.rectangle, E8TAxisProd0236Geometry.sLower, E8TAxisProd0236Geometry.sUpper, E8TAxisProd0236Geometry.tLower, E8TAxisProd0236Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0236

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0237 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0237
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0237Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0237Geometry.rectangle, E8TAxisProd0237Geometry.sLower, E8TAxisProd0237Geometry.sUpper, E8TAxisProd0237Geometry.tLower, E8TAxisProd0237Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0237

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0238 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0238
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0238Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0238Geometry.rectangle, E8TAxisProd0238Geometry.sLower, E8TAxisProd0238Geometry.sUpper, E8TAxisProd0238Geometry.tLower, E8TAxisProd0238Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0238

end


