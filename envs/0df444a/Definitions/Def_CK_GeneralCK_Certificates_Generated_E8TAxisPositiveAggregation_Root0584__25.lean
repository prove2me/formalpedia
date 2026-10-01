-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0584__25
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0584__25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:57:46.833436+00:00
-- url     : https://prove2.me/theorems/cf6ab76b-1a2f-4a7c-b21d-f87964b727f6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0584 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0585, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0584 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0585, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0586, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0587, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0588, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0589, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0590, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0591, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0592, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0593, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0594, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0595, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0596, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0597, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0598, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0599, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0600, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0601, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0602, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0603, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0604, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0605, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0606, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0607, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0608)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0584 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0585, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0586, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0587, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0588, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0589, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0590, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0591, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0592, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0593, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0594, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0595, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0596, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0597, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0598, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0599, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0600, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0601, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0602, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0603, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0604, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0605, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0606, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0607, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0608)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0584 (+24 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0585, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0586, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0587, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0588, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0589, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0590, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0591, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0592, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0593, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0594, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0595, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0596, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0597, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0598, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0599, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0600, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0601, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0602, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0603, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0604, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0605, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0606, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0607, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0608) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0584 (+24 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0585, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0586, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0587, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0588, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0589, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0590, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0591, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0592, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0593, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0594, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0595, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0596, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0597, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0598, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0599, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0600, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0601, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0602, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0603, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0604, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0605, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0606, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0607, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0608).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0604Certified__17

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0584 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0584
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0584Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0584Geometry.rectangle, E8TAxisProd0584Geometry.sLower, E8TAxisProd0584Geometry.sUpper, E8TAxisProd0584Geometry.tLower, E8TAxisProd0584Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0584

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0585 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0585
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0585Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0585Geometry.rectangle, E8TAxisProd0585Geometry.sLower, E8TAxisProd0585Geometry.sUpper, E8TAxisProd0585Geometry.tLower, E8TAxisProd0585Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0585

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0586 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0586
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0586Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0586Geometry.rectangle, E8TAxisProd0586Geometry.sLower, E8TAxisProd0586Geometry.sUpper, E8TAxisProd0586Geometry.tLower, E8TAxisProd0586Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0586

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0587 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0587
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (325 / 128 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0587Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0587Geometry.rectangle, E8TAxisProd0587Geometry.sLower, E8TAxisProd0587Geometry.sUpper, E8TAxisProd0587Geometry.tLower, E8TAxisProd0587Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0587

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0588 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0588
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0588Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0588Geometry.rectangle, E8TAxisProd0588Geometry.sLower, E8TAxisProd0588Geometry.sUpper, E8TAxisProd0588Geometry.tLower, E8TAxisProd0588Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0588

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0589 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0589
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0589Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0589Geometry.rectangle, E8TAxisProd0589Geometry.sLower, E8TAxisProd0589Geometry.sUpper, E8TAxisProd0589Geometry.tLower, E8TAxisProd0589Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0589

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0590 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0590
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0590Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0590Geometry.rectangle, E8TAxisProd0590Geometry.sLower, E8TAxisProd0590Geometry.sUpper, E8TAxisProd0590Geometry.tLower, E8TAxisProd0590Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0590

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0591 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0591
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0591Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0591Geometry.rectangle, E8TAxisProd0591Geometry.sLower, E8TAxisProd0591Geometry.sUpper, E8TAxisProd0591Geometry.tLower, E8TAxisProd0591Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0591

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0592 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0592
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0592Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0592Geometry.rectangle, E8TAxisProd0592Geometry.sLower, E8TAxisProd0592Geometry.sUpper, E8TAxisProd0592Geometry.tLower, E8TAxisProd0592Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0592

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0593 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0593
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0593Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0593Geometry.rectangle, E8TAxisProd0593Geometry.sLower, E8TAxisProd0593Geometry.sUpper, E8TAxisProd0593Geometry.tLower, E8TAxisProd0593Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0593

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0594 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0594
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0594Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0594Geometry.rectangle, E8TAxisProd0594Geometry.sLower, E8TAxisProd0594Geometry.sUpper, E8TAxisProd0594Geometry.tLower, E8TAxisProd0594Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0594

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0595 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0595
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0595Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0595Geometry.rectangle, E8TAxisProd0595Geometry.sLower, E8TAxisProd0595Geometry.sUpper, E8TAxisProd0595Geometry.tLower, E8TAxisProd0595Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0595

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0596 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0596
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0596Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0596Geometry.rectangle, E8TAxisProd0596Geometry.sLower, E8TAxisProd0596Geometry.sUpper, E8TAxisProd0596Geometry.tLower, E8TAxisProd0596Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0596

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0597 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0597
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0597Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0597Geometry.rectangle, E8TAxisProd0597Geometry.sLower, E8TAxisProd0597Geometry.sUpper, E8TAxisProd0597Geometry.tLower, E8TAxisProd0597Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0597

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0598 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0598
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0598Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0598Geometry.rectangle, E8TAxisProd0598Geometry.sLower, E8TAxisProd0598Geometry.sUpper, E8TAxisProd0598Geometry.tLower, E8TAxisProd0598Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0598

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0599 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0599
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0599Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0599Geometry.rectangle, E8TAxisProd0599Geometry.sLower, E8TAxisProd0599Geometry.sUpper, E8TAxisProd0599Geometry.tLower, E8TAxisProd0599Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0599

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0600 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0600
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0600Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0600Geometry.rectangle, E8TAxisProd0600Geometry.sLower, E8TAxisProd0600Geometry.sUpper, E8TAxisProd0600Geometry.tLower, E8TAxisProd0600Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0600

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0601 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0601
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0601Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0601Geometry.rectangle, E8TAxisProd0601Geometry.sLower, E8TAxisProd0601Geometry.sUpper, E8TAxisProd0601Geometry.tLower, E8TAxisProd0601Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0601

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0602 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0602
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0602Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0602Geometry.rectangle, E8TAxisProd0602Geometry.sLower, E8TAxisProd0602Geometry.sUpper, E8TAxisProd0602Geometry.tLower, E8TAxisProd0602Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0602

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0603 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0603
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(151 / 64 : ℝ), (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0603Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0603Geometry.rectangle, E8TAxisProd0603Geometry.sLower, E8TAxisProd0603Geometry.sUpper, E8TAxisProd0603Geometry.tLower, E8TAxisProd0603Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0603

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0604 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0604
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0604Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0604Geometry.rectangle, E8TAxisProd0604Geometry.sLower, E8TAxisProd0604Geometry.sUpper, E8TAxisProd0604Geometry.tLower, E8TAxisProd0604Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0604

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0605 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0605
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0605Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0605Geometry.rectangle, E8TAxisProd0605Geometry.sLower, E8TAxisProd0605Geometry.sUpper, E8TAxisProd0605Geometry.tLower, E8TAxisProd0605Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0605

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0606 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0606
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (151 / 64 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0606Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0606Geometry.rectangle, E8TAxisProd0606Geometry.sLower, E8TAxisProd0606Geometry.sUpper, E8TAxisProd0606Geometry.tLower, E8TAxisProd0606Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0606

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0607 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0607
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0607Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0607Geometry.rectangle, E8TAxisProd0607Geometry.sLower, E8TAxisProd0607Geometry.sUpper, E8TAxisProd0607Geometry.tLower, E8TAxisProd0607Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0607

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0608 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0608
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(325 / 128 : ℝ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0608Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0608Geometry.rectangle, E8TAxisProd0608Geometry.sLower, E8TAxisProd0608Geometry.sUpper, E8TAxisProd0608Geometry.tLower, E8TAxisProd0608Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0608

end


