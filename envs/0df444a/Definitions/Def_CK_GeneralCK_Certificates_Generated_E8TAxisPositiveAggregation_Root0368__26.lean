-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0368__26
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0368__26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:22:53.955977+00:00
-- url     : https://prove2.me/theorems/765f197b-6c16-4510-8513-d26088125ab6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0368 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0369, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0368 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0369, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0370, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0371, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0372, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0373, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0374, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0375, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0376, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0377, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0378, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0379, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0380, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0381, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0382, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0383, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0384, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0385, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0386, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0387, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0388, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0389, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0390, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0391, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0392, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0393)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0368 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0369, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0370, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0371, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0372, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0373, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0374, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0375, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0376, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0377, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0378, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0379, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0380, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0381, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0382, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0383, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0384, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0385, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0386, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0387, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0388, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0389, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0390, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0391, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0392, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0393)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0368 (+25 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0369, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0370, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0371, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0372, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0373, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0374, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0375, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0376, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0377, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0378, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0379, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0380, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0381, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0382, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0383, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0384, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0385, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0386, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0387, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0388, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0389, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0390, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0391, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0392, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0393) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0368 (+25 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0369, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0370, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0371, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0372, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0373, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0374, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0375, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0376, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0377, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0378, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0379, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0380, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0381, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0382, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0383, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0384, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0385, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0386, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0387, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0388, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0389, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0390, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0391, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0392, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0393).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357Certified__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0379Certified__20

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0368 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0368
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0368Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0368Geometry.rectangle, E8TAxisProd0368Geometry.sLower, E8TAxisProd0368Geometry.sUpper, E8TAxisProd0368Geometry.tLower, E8TAxisProd0368Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0368

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0369 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0369
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0369Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0369Geometry.rectangle, E8TAxisProd0369Geometry.sLower, E8TAxisProd0369Geometry.sUpper, E8TAxisProd0369Geometry.tLower, E8TAxisProd0369Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0369

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0370 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0370
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0370Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0370Geometry.rectangle, E8TAxisProd0370Geometry.sLower, E8TAxisProd0370Geometry.sUpper, E8TAxisProd0370Geometry.tLower, E8TAxisProd0370Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0370

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0371 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0371
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0371Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0371Geometry.rectangle, E8TAxisProd0371Geometry.sLower, E8TAxisProd0371Geometry.sUpper, E8TAxisProd0371Geometry.tLower, E8TAxisProd0371Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0371

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0372 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0372
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0372Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0372Geometry.rectangle, E8TAxisProd0372Geometry.sLower, E8TAxisProd0372Geometry.sUpper, E8TAxisProd0372Geometry.tLower, E8TAxisProd0372Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0372

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0373 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0373
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0373Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0373Geometry.rectangle, E8TAxisProd0373Geometry.sLower, E8TAxisProd0373Geometry.sUpper, E8TAxisProd0373Geometry.tLower, E8TAxisProd0373Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0373

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0374 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0374
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0374Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0374Geometry.rectangle, E8TAxisProd0374Geometry.sLower, E8TAxisProd0374Geometry.sUpper, E8TAxisProd0374Geometry.tLower, E8TAxisProd0374Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0374

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0375 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0375
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0375Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0375Geometry.rectangle, E8TAxisProd0375Geometry.sLower, E8TAxisProd0375Geometry.sUpper, E8TAxisProd0375Geometry.tLower, E8TAxisProd0375Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0375

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0376 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0376
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (63 / 20 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0376Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0376Geometry.rectangle, E8TAxisProd0376Geometry.sLower, E8TAxisProd0376Geometry.sUpper, E8TAxisProd0376Geometry.tLower, E8TAxisProd0376Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0376

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0377 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0377
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(197 / 64 : ℝ), (15570312500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0377Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0377Geometry.rectangle, E8TAxisProd0377Geometry.sLower, E8TAxisProd0377Geometry.sUpper, E8TAxisProd0377Geometry.tLower, E8TAxisProd0377Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0377

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0378 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0378
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (197 / 64 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0378Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0378Geometry.rectangle, E8TAxisProd0378Geometry.sLower, E8TAxisProd0378Geometry.sUpper, E8TAxisProd0378Geometry.tLower, E8TAxisProd0378Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0378

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0379 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0379
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3802734375000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0379Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0379Geometry.rectangle, E8TAxisProd0379Geometry.sLower, E8TAxisProd0379Geometry.sUpper, E8TAxisProd0379Geometry.tLower, E8TAxisProd0379Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0379

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0380 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0380
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0380Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0380Geometry.rectangle, E8TAxisProd0380Geometry.sLower, E8TAxisProd0380Geometry.sUpper, E8TAxisProd0380Geometry.tLower, E8TAxisProd0380Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0380

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0381 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0381
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0381Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0381Geometry.rectangle, E8TAxisProd0381Geometry.sLower, E8TAxisProd0381Geometry.sUpper, E8TAxisProd0381Geometry.tLower, E8TAxisProd0381Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0381

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0382 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0382
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0382Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0382Geometry.rectangle, E8TAxisProd0382Geometry.sLower, E8TAxisProd0382Geometry.sUpper, E8TAxisProd0382Geometry.tLower, E8TAxisProd0382Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0382

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0383 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0383
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0383Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0383Geometry.rectangle, E8TAxisProd0383Geometry.sLower, E8TAxisProd0383Geometry.sUpper, E8TAxisProd0383Geometry.tLower, E8TAxisProd0383Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0383

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0384 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0384
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0384Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0384Geometry.rectangle, E8TAxisProd0384Geometry.sLower, E8TAxisProd0384Geometry.sUpper, E8TAxisProd0384Geometry.tLower, E8TAxisProd0384Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0384

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0385 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0385
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0385Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0385Geometry.rectangle, E8TAxisProd0385Geometry.sLower, E8TAxisProd0385Geometry.sUpper, E8TAxisProd0385Geometry.tLower, E8TAxisProd0385Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0385

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0386 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0386
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0386Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0386Geometry.rectangle, E8TAxisProd0386Geometry.sLower, E8TAxisProd0386Geometry.sUpper, E8TAxisProd0386Geometry.tLower, E8TAxisProd0386Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0386

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0387 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0387
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0387Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0387Geometry.rectangle, E8TAxisProd0387Geometry.sLower, E8TAxisProd0387Geometry.sUpper, E8TAxisProd0387Geometry.tLower, E8TAxisProd0387Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0387

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0388 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0388
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (15031250000000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0388Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0388Geometry.rectangle, E8TAxisProd0388Geometry.sLower, E8TAxisProd0388Geometry.sUpper, E8TAxisProd0388Geometry.tLower, E8TAxisProd0388Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0388

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0389 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0389
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7425781250000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0389Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0389Geometry.rectangle, E8TAxisProd0389Geometry.sLower, E8TAxisProd0389Geometry.sUpper, E8TAxisProd0389Geometry.tLower, E8TAxisProd0389Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0389

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0390 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0390
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (7335937500000000000000000000000000000000000000000000000001911710293359 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0390Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0390Geometry.rectangle, E8TAxisProd0390Geometry.sLower, E8TAxisProd0390Geometry.sUpper, E8TAxisProd0390Geometry.tLower, E8TAxisProd0390Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0390

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0391 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0391
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (2898437500000000000000000000000000000000000000000000000000637236764453 / 1000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0391Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0391Geometry.rectangle, E8TAxisProd0391Geometry.sLower, E8TAxisProd0391Geometry.sUpper, E8TAxisProd0391Geometry.tLower, E8TAxisProd0391Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0391

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0392 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0392
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0392Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0392Geometry.rectangle, E8TAxisProd0392Geometry.sLower, E8TAxisProd0392Geometry.sUpper, E8TAxisProd0392Geometry.tLower, E8TAxisProd0392Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0392

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0393 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0393
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0393Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0393Geometry.rectangle, E8TAxisProd0393Geometry.sLower, E8TAxisProd0393Geometry.sUpper, E8TAxisProd0393Geometry.tLower, E8TAxisProd0393Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0393

end


