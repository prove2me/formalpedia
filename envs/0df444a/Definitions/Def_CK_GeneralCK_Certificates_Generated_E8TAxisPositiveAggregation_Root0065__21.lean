-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0065__21
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0065__21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:32:20.475273+00:00
-- url     : https://prove2.me/theorems/35c9f000-738b-4b48-ad36-252cd67eb18a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0065 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0066, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0065 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0066, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0067, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0068, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0069, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0070, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0071, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0072, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0073, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0074, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0075, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0076, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0077, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0078, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0079, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0080, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0081, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0082, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0083, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0084, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0085)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0065 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0066, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0067, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0068, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0069, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0070, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0071, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0072, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0073, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0074, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0075, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0076, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0077, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0078, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0079, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0080, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0081, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0082, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0083, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0084, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0085)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0065 (+20 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0066, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0067, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0068, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0069, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0070, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0071, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0072, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0073, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0074, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0075, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0076, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0077, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0078, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0079, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0080, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0081, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0082, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0083, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0084, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0085) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0065 (+20 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0066, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0067, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0068, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0069, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0070, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0071, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0072, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0073, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0074, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0075, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0076, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0077, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0078, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0079, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0080, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0081, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0082, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0083, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0084, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0085).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0064Certified__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LCertified__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RCertified__11

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0065 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0065
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(15 / 16 : ℝ), (1 / 1 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0065Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0065Geometry.rectangle, E8TAxisProd0065Geometry.sLower, E8TAxisProd0065Geometry.sUpper, E8TAxisProd0065Geometry.tLower, E8TAxisProd0065Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0065

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0066 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0066
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(7 / 8 : ℝ), (15 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0066Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0066Geometry.rectangle, E8TAxisProd0066Geometry.sLower, E8TAxisProd0066Geometry.sUpper, E8TAxisProd0066Geometry.tLower, E8TAxisProd0066Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0066

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0067 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0067
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(13 / 16 : ℝ), (7 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0067Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0067Geometry.rectangle, E8TAxisProd0067Geometry.sLower, E8TAxisProd0067Geometry.sUpper, E8TAxisProd0067Geometry.tLower, E8TAxisProd0067Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0067

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0068 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0068
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 4 : ℝ), (13 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0068Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0068Geometry.rectangle, E8TAxisProd0068Geometry.sLower, E8TAxisProd0068Geometry.sUpper, E8TAxisProd0068Geometry.tLower, E8TAxisProd0068Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0068

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0069 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0069
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 16 : ℝ), (3 / 4 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0069Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0069Geometry.rectangle, E8TAxisProd0069Geometry.sLower, E8TAxisProd0069Geometry.sUpper, E8TAxisProd0069Geometry.tLower, E8TAxisProd0069Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0069

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0070 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0070
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 8 : ℝ), (11 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0070Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0070Geometry.rectangle, E8TAxisProd0070Geometry.sLower, E8TAxisProd0070Geometry.sUpper, E8TAxisProd0070Geometry.tLower, E8TAxisProd0070Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0070

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0071 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0071
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 16 : ℝ), (3 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0071Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0071Geometry.rectangle, E8TAxisProd0071Geometry.sLower, E8TAxisProd0071Geometry.sUpper, E8TAxisProd0071Geometry.tLower, E8TAxisProd0071Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0071

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0072 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0072
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 8 : ℝ), (11 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0072Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0072Geometry.rectangle, E8TAxisProd0072Geometry.sLower, E8TAxisProd0072Geometry.sUpper, E8TAxisProd0072Geometry.tLower, E8TAxisProd0072Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0072

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0073 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0073
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0073LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0073LGeometry.rectangle, E8TAxisProd0073LGeometry.sLower, E8TAxisProd0073LGeometry.sUpper, E8TAxisProd0073LGeometry.tLower, E8TAxisProd0073LGeometry.tUpper]
  ·
    convert E8TAxisProd0073RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0073RGeometry.rectangle, E8TAxisProd0073RGeometry.sLower, E8TAxisProd0073RGeometry.sUpper, E8TAxisProd0073RGeometry.tLower, E8TAxisProd0073RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0073

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0074 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0074
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0074LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0074LGeometry.rectangle, E8TAxisProd0074LGeometry.sLower, E8TAxisProd0074LGeometry.sUpper, E8TAxisProd0074LGeometry.tLower, E8TAxisProd0074LGeometry.tUpper]
  ·
    convert E8TAxisProd0074RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0074RGeometry.rectangle, E8TAxisProd0074RGeometry.sLower, E8TAxisProd0074RGeometry.sUpper, E8TAxisProd0074RGeometry.tLower, E8TAxisProd0074RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0074

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0075 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0075
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 32 : ℝ), (9 / 16 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0075Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0075Geometry.rectangle, E8TAxisProd0075Geometry.sLower, E8TAxisProd0075Geometry.sUpper, E8TAxisProd0075Geometry.tLower, E8TAxisProd0075Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0075

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0076 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0076
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 2 : ℝ), (17 / 32 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0076Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0076Geometry.rectangle, E8TAxisProd0076Geometry.sLower, E8TAxisProd0076Geometry.sUpper, E8TAxisProd0076Geometry.tLower, E8TAxisProd0076Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0076

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0077 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0077
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 32 : ℝ), (9 / 16 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0077Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0077Geometry.rectangle, E8TAxisProd0077Geometry.sLower, E8TAxisProd0077Geometry.sUpper, E8TAxisProd0077Geometry.tLower, E8TAxisProd0077Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0077

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0078 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0078
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 2 : ℝ), (17 / 32 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0078Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0078Geometry.rectangle, E8TAxisProd0078Geometry.sLower, E8TAxisProd0078Geometry.sUpper, E8TAxisProd0078Geometry.tLower, E8TAxisProd0078Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0078

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0079 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0079
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0079LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0079LGeometry.rectangle, E8TAxisProd0079LGeometry.sLower, E8TAxisProd0079LGeometry.sUpper, E8TAxisProd0079LGeometry.tLower, E8TAxisProd0079LGeometry.tUpper]
  ·
    convert E8TAxisProd0079RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0079RGeometry.rectangle, E8TAxisProd0079RGeometry.sLower, E8TAxisProd0079RGeometry.sUpper, E8TAxisProd0079RGeometry.tLower, E8TAxisProd0079RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0079

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0080 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0080
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0080LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0080LGeometry.rectangle, E8TAxisProd0080LGeometry.sLower, E8TAxisProd0080LGeometry.sUpper, E8TAxisProd0080LGeometry.tLower, E8TAxisProd0080LGeometry.tUpper]
  ·
    convert E8TAxisProd0080RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0080RGeometry.rectangle, E8TAxisProd0080RGeometry.sLower, E8TAxisProd0080RGeometry.sUpper, E8TAxisProd0080RGeometry.tLower, E8TAxisProd0080RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0080

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0081 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0081
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 32 : ℝ), (9 / 16 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0081Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0081Geometry.rectangle, E8TAxisProd0081Geometry.sLower, E8TAxisProd0081Geometry.sUpper, E8TAxisProd0081Geometry.tLower, E8TAxisProd0081Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0081

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0082 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0082
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 2 : ℝ), (17 / 32 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0082Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0082Geometry.rectangle, E8TAxisProd0082Geometry.sLower, E8TAxisProd0082Geometry.sUpper, E8TAxisProd0082Geometry.tLower, E8TAxisProd0082Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0082

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0083 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0083
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(17 / 32 : ℝ), (9 / 16 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0083Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0083Geometry.rectangle, E8TAxisProd0083Geometry.sLower, E8TAxisProd0083Geometry.sUpper, E8TAxisProd0083Geometry.tLower, E8TAxisProd0083Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0083

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0084 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0084
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 2 : ℝ), (17 / 32 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0084Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0084Geometry.rectangle, E8TAxisProd0084Geometry.sLower, E8TAxisProd0084Geometry.sUpper, E8TAxisProd0084Geometry.tLower, E8TAxisProd0084Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0084

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0085 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0085
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11 / 16 : ℝ), (3 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0085Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0085Geometry.rectangle, E8TAxisProd0085Geometry.sLower, E8TAxisProd0085Geometry.sUpper, E8TAxisProd0085Geometry.tLower, E8TAxisProd0085Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0085

end


