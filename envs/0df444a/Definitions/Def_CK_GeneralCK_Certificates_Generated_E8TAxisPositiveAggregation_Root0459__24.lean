-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0459__24
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0459__24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:01:00.549066+00:00
-- url     : https://prove2.me/theorems/75696401-0d52-45f5-9e8e-b36b36cc3e75
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0459 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0460, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0459 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0460, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0461, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0462, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0463, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0464, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0465, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0466, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0467, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0468, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0469, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0470, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0471, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0472, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0473, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0474, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0475, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0476, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0477, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0478, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0479, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0480, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0481, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0482)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0459 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0460, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0461, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0462, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0463, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0464, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0465, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0466, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0467, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0468, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0469, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0470, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0471, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0472, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0473, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0474, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0475, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0476, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0477, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0478, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0479, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0480, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0481, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0482)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0459 (+23 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0460, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0461, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0462, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0463, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0464, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0465, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0466, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0467, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0468, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0469, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0470, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0471, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0472, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0473, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0474, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0475, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0476, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0477, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0478, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0479, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0480, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0481, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0482) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0459 (+23 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0460, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0461, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0462, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0463, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0464, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0465, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0466, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0467, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0468, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0469, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0470, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0471, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0472, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0473, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0474, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0475, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0476, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0477, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0478, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0479, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0480, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0481, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0482).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0458Certified__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0473Certified__15

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0459 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0459
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0459Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0459Geometry.rectangle, E8TAxisProd0459Geometry.sLower, E8TAxisProd0459Geometry.sUpper, E8TAxisProd0459Geometry.tLower, E8TAxisProd0459Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0459

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0460 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0460
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0460Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0460Geometry.rectangle, E8TAxisProd0460Geometry.sLower, E8TAxisProd0460Geometry.sUpper, E8TAxisProd0460Geometry.tLower, E8TAxisProd0460Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0460

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0461 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0461
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0461Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0461Geometry.rectangle, E8TAxisProd0461Geometry.sLower, E8TAxisProd0461Geometry.sUpper, E8TAxisProd0461Geometry.tLower, E8TAxisProd0461Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0461

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0462 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0462
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0462Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0462Geometry.rectangle, E8TAxisProd0462Geometry.sLower, E8TAxisProd0462Geometry.sUpper, E8TAxisProd0462Geometry.tLower, E8TAxisProd0462Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0462

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0463 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0463
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0463Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0463Geometry.rectangle, E8TAxisProd0463Geometry.sLower, E8TAxisProd0463Geometry.sUpper, E8TAxisProd0463Geometry.tLower, E8TAxisProd0463Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0463

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0464 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0464
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0464Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0464Geometry.rectangle, E8TAxisProd0464Geometry.sLower, E8TAxisProd0464Geometry.sUpper, E8TAxisProd0464Geometry.tLower, E8TAxisProd0464Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0464

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0465 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0465
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0465Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0465Geometry.rectangle, E8TAxisProd0465Geometry.sLower, E8TAxisProd0465Geometry.sUpper, E8TAxisProd0465Geometry.tLower, E8TAxisProd0465Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0465

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0466 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0466
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0466Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0466Geometry.rectangle, E8TAxisProd0466Geometry.sLower, E8TAxisProd0466Geometry.sUpper, E8TAxisProd0466Geometry.tLower, E8TAxisProd0466Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0466

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0467 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0467
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0467Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0467Geometry.rectangle, E8TAxisProd0467Geometry.sLower, E8TAxisProd0467Geometry.sUpper, E8TAxisProd0467Geometry.tLower, E8TAxisProd0467Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0467

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0468 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0468
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0468Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0468Geometry.rectangle, E8TAxisProd0468Geometry.sLower, E8TAxisProd0468Geometry.sUpper, E8TAxisProd0468Geometry.tLower, E8TAxisProd0468Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0468

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0469 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0469
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0469Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0469Geometry.rectangle, E8TAxisProd0469Geometry.sLower, E8TAxisProd0469Geometry.sUpper, E8TAxisProd0469Geometry.tLower, E8TAxisProd0469Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0469

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0470 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0470
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0470Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0470Geometry.rectangle, E8TAxisProd0470Geometry.sLower, E8TAxisProd0470Geometry.sUpper, E8TAxisProd0470Geometry.tLower, E8TAxisProd0470Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0470

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0471 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0471
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0471Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0471Geometry.rectangle, E8TAxisProd0471Geometry.sLower, E8TAxisProd0471Geometry.sUpper, E8TAxisProd0471Geometry.tLower, E8TAxisProd0471Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0471

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0472 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0472
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0472Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0472Geometry.rectangle, E8TAxisProd0472Geometry.sLower, E8TAxisProd0472Geometry.sUpper, E8TAxisProd0472Geometry.tLower, E8TAxisProd0472Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0472

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0473 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0473
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0473Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0473Geometry.rectangle, E8TAxisProd0473Geometry.sLower, E8TAxisProd0473Geometry.sUpper, E8TAxisProd0473Geometry.tLower, E8TAxisProd0473Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0473

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0474 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0474
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0474Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0474Geometry.rectangle, E8TAxisProd0474Geometry.sLower, E8TAxisProd0474Geometry.sUpper, E8TAxisProd0474Geometry.tLower, E8TAxisProd0474Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0474

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0475 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0475
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0475Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0475Geometry.rectangle, E8TAxisProd0475Geometry.sLower, E8TAxisProd0475Geometry.sUpper, E8TAxisProd0475Geometry.tLower, E8TAxisProd0475Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0475

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0476 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0476
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0476Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0476Geometry.rectangle, E8TAxisProd0476Geometry.sLower, E8TAxisProd0476Geometry.sUpper, E8TAxisProd0476Geometry.tLower, E8TAxisProd0476Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0476

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0477 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0477
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0477Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0477Geometry.rectangle, E8TAxisProd0477Geometry.sLower, E8TAxisProd0477Geometry.sUpper, E8TAxisProd0477Geometry.tLower, E8TAxisProd0477Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0477

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0478 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0478
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0478Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0478Geometry.rectangle, E8TAxisProd0478Geometry.sLower, E8TAxisProd0478Geometry.sUpper, E8TAxisProd0478Geometry.tLower, E8TAxisProd0478Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0478

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0479 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0479
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0479Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0479Geometry.rectangle, E8TAxisProd0479Geometry.sLower, E8TAxisProd0479Geometry.sUpper, E8TAxisProd0479Geometry.tLower, E8TAxisProd0479Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0479

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0480 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0480
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0480Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0480Geometry.rectangle, E8TAxisProd0480Geometry.sLower, E8TAxisProd0480Geometry.sUpper, E8TAxisProd0480Geometry.tLower, E8TAxisProd0480Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0480

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0481 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0481
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0481Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0481Geometry.rectangle, E8TAxisProd0481Geometry.sLower, E8TAxisProd0481Geometry.sUpper, E8TAxisProd0481Geometry.tLower, E8TAxisProd0481Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0481

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0482 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0482
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0482Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0482Geometry.rectangle, E8TAxisProd0482Geometry.sLower, E8TAxisProd0482Geometry.sUpper, E8TAxisProd0482Geometry.tLower, E8TAxisProd0482Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0482

end


