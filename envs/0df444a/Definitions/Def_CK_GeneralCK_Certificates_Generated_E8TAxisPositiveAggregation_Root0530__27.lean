-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0530__27
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0530__27
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:55:14.146879+00:00
-- url     : https://prove2.me/theorems/3e7600f9-940f-4952-8ca3-12948166f939
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0530 (+26 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0531, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0530 (+26 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0531, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0532, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0533, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0534, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0535, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0536, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0537, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0538, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0539, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0540, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0541, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0542, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0543, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0544, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0545, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0546, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0547, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0548, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0549, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0550, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0551, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0552, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0553, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0554, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0555, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0556)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0530 (+26 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0531, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0532, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0533, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0534, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0535, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0536, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0537, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0538, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0539, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0540, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0541, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0542, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0543, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0544, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0545, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0546, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0547, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0548, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0549, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0550, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0551, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0552, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0553, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0554, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0555, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0556)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0530 (+26 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0531, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0532, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0533, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0534, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0535, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0536, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0537, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0538, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0539, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0540, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0541, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0542, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0543, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0544, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0545, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0546, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0547, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0548, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0549, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0550, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0551, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0552, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0553, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0554, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0555, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0556) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0530 (+26 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0531, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0532, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0533, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0534, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0535, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0536, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0537, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0538, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0539, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0540, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0541, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0542, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0543, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0544, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0545, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0546, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0547, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0548, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0549, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0550, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0551, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0552, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0553, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0554, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0555, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0556).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0523Certified__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0543Certified__18

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0530 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0530
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0530Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0530Geometry.rectangle, E8TAxisProd0530Geometry.sLower, E8TAxisProd0530Geometry.sUpper, E8TAxisProd0530Geometry.tLower, E8TAxisProd0530Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0530

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0531 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0531
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0531Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0531Geometry.rectangle, E8TAxisProd0531Geometry.sLower, E8TAxisProd0531Geometry.sUpper, E8TAxisProd0531Geometry.tLower, E8TAxisProd0531Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0531

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0532 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0532
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0532Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0532Geometry.rectangle, E8TAxisProd0532Geometry.sLower, E8TAxisProd0532Geometry.sUpper, E8TAxisProd0532Geometry.tLower, E8TAxisProd0532Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0532

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0533 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0533
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0533Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0533Geometry.rectangle, E8TAxisProd0533Geometry.sLower, E8TAxisProd0533Geometry.sUpper, E8TAxisProd0533Geometry.tLower, E8TAxisProd0533Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0533

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0534 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0534
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0534Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0534Geometry.rectangle, E8TAxisProd0534Geometry.sLower, E8TAxisProd0534Geometry.sUpper, E8TAxisProd0534Geometry.tLower, E8TAxisProd0534Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0534

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0535 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0535
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4687500000000000000000000000000000000000000000000000000000497841222229 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0535Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0535Geometry.rectangle, E8TAxisProd0535Geometry.sLower, E8TAxisProd0535Geometry.sUpper, E8TAxisProd0535Geometry.tLower, E8TAxisProd0535Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0535

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0536 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0536
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0536Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0536Geometry.rectangle, E8TAxisProd0536Geometry.sLower, E8TAxisProd0536Geometry.sUpper, E8TAxisProd0536Geometry.tLower, E8TAxisProd0536Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0536

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0537 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0537
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0537Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0537Geometry.rectangle, E8TAxisProd0537Geometry.sLower, E8TAxisProd0537Geometry.sUpper, E8TAxisProd0537Geometry.tLower, E8TAxisProd0537Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0537

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0538 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0538
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0538Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0538Geometry.rectangle, E8TAxisProd0538Geometry.sLower, E8TAxisProd0538Geometry.sUpper, E8TAxisProd0538Geometry.tLower, E8TAxisProd0538Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0538

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0539 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0539
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0539Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0539Geometry.rectangle, E8TAxisProd0539Geometry.sLower, E8TAxisProd0539Geometry.sUpper, E8TAxisProd0539Geometry.tLower, E8TAxisProd0539Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0539

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0540 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0540
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0540Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0540Geometry.rectangle, E8TAxisProd0540Geometry.sLower, E8TAxisProd0540Geometry.sUpper, E8TAxisProd0540Geometry.tLower, E8TAxisProd0540Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0540

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0541 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0541
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0541Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0541Geometry.rectangle, E8TAxisProd0541Geometry.sLower, E8TAxisProd0541Geometry.sUpper, E8TAxisProd0541Geometry.tLower, E8TAxisProd0541Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0541

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0542 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0542
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0542Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0542Geometry.rectangle, E8TAxisProd0542Geometry.sLower, E8TAxisProd0542Geometry.sUpper, E8TAxisProd0542Geometry.tLower, E8TAxisProd0542Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0542

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0543 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0543
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2 / 1 : ℝ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0543Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0543Geometry.rectangle, E8TAxisProd0543Geometry.sLower, E8TAxisProd0543Geometry.sUpper, E8TAxisProd0543Geometry.tLower, E8TAxisProd0543Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0543

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0544 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0544
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0544Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0544Geometry.rectangle, E8TAxisProd0544Geometry.sLower, E8TAxisProd0544Geometry.sUpper, E8TAxisProd0544Geometry.tLower, E8TAxisProd0544Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0544

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0545 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0545
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0545Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0545Geometry.rectangle, E8TAxisProd0545Geometry.sLower, E8TAxisProd0545Geometry.sUpper, E8TAxisProd0545Geometry.tLower, E8TAxisProd0545Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0545

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0546 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0546
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0546Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0546Geometry.rectangle, E8TAxisProd0546Geometry.sLower, E8TAxisProd0546Geometry.sUpper, E8TAxisProd0546Geometry.tLower, E8TAxisProd0546Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0546

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0547 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0547
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0547Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0547Geometry.rectangle, E8TAxisProd0547Geometry.sLower, E8TAxisProd0547Geometry.sUpper, E8TAxisProd0547Geometry.tLower, E8TAxisProd0547Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0547

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0548 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0548
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0548Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0548Geometry.rectangle, E8TAxisProd0548Geometry.sLower, E8TAxisProd0548Geometry.sUpper, E8TAxisProd0548Geometry.tLower, E8TAxisProd0548Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0548

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0549 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0549
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0549Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0549Geometry.rectangle, E8TAxisProd0549Geometry.sLower, E8TAxisProd0549Geometry.sUpper, E8TAxisProd0549Geometry.tLower, E8TAxisProd0549Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0549

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0550 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0550
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0550Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0550Geometry.rectangle, E8TAxisProd0550Geometry.sLower, E8TAxisProd0550Geometry.sUpper, E8TAxisProd0550Geometry.tLower, E8TAxisProd0550Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0550

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0551 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0551
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (279 / 128 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (13749999999999999999999999999999999999999999999999999999998805181066651 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0551Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0551Geometry.rectangle, E8TAxisProd0551Geometry.sLower, E8TAxisProd0551Geometry.sUpper, E8TAxisProd0551Geometry.tLower, E8TAxisProd0551Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0551

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0552 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0552
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0552Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0552Geometry.rectangle, E8TAxisProd0552Geometry.sLower, E8TAxisProd0552Geometry.sUpper, E8TAxisProd0552Geometry.tLower, E8TAxisProd0552Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0552

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0553 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0553
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0553Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0553Geometry.rectangle, E8TAxisProd0553Geometry.sLower, E8TAxisProd0553Geometry.sUpper, E8TAxisProd0553Geometry.tLower, E8TAxisProd0553Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0553

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0554 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0554
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0554Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0554Geometry.rectangle, E8TAxisProd0554Geometry.sLower, E8TAxisProd0554Geometry.sUpper, E8TAxisProd0554Geometry.tLower, E8TAxisProd0554Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0554

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0555 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0555
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0555Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0555Geometry.rectangle, E8TAxisProd0555Geometry.sLower, E8TAxisProd0555Geometry.sUpper, E8TAxisProd0555Geometry.tLower, E8TAxisProd0555Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0555

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0556 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0556
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(279 / 128 : ℝ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5624999999999999999999999999999999999999999999999999999998606044577759 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0556Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0556Geometry.rectangle, E8TAxisProd0556Geometry.sLower, E8TAxisProd0556Geometry.sUpper, E8TAxisProd0556Geometry.tLower, E8TAxisProd0556Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0556

end


