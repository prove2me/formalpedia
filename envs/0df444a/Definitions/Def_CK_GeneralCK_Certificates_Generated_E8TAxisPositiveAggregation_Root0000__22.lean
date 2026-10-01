-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0000__22
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisPositiveAggregation_Root0000__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:20:16.153869+00:00
-- url     : https://prove2.me/theorems/bfc1fa00-aa19-44c7-ad88-6eb05bce8895
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0000 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0001, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0000 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0001, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0002, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0003, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0004, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0005, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0006, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0007, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0008, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0009, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0010, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0011, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0012, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0013, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0014, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0015, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0016, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0017, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0018, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0019, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0020, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0021)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0000 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0001, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0002, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0003, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0004, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0005, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0006, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0007, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0008, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0009, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0010, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0011, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0012, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0013, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0014, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0015, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0016, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0017, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0018, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0019, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0020, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0021)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0000 (+21 modules: GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0001, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0002, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0003, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0004, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0005, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0006, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0007, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0008, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0009, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0010, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0011, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0012, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0013, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0014, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0015, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0016, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0017, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0018, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0019, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0020, GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0021) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0000 (+21 modules: GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0001, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0002, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0003, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0004, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0005, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0006, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0007, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0008, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0009, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0010, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0011, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0012, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0013, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0014, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0015, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0016, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0017, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0018, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0019, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0020, GeneralCK/Certificates/Generated/E8TAxisPositiveAggregation/Root0021).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPositiveAggregationKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LCertified__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RCertified__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001Certified__19
import Definitions.Def_GeneralCK_E8_Prod0001_leaf_data
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0020Certified__22

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0000 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0000
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 10 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := (.splitS (7500000000000000000000000000000000000000000000000000000000637236764453 / 80000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0000LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0000LGeometry.rectangle, E8TAxisProd0000LGeometry.sLower, E8TAxisProd0000LGeometry.sUpper, E8TAxisProd0000LGeometry.tLower, E8TAxisProd0000LGeometry.tUpper]
  ·
    convert E8TAxisProd0000RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0000RGeometry.rectangle, E8TAxisProd0000RGeometry.sLower, E8TAxisProd0000RGeometry.sUpper, E8TAxisProd0000RGeometry.tLower, E8TAxisProd0000RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0000

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0001 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0001
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000




theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0001Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0001Geometry.rectangle, E8TAxisProd0001Geometry.sLower, E8TAxisProd0001Geometry.sUpper, E8TAxisProd0001Geometry.tLower, E8TAxisProd0001Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0001

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0002 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0002
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(3 / 40 : ℝ), (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0002Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0002Geometry.rectangle, E8TAxisProd0002Geometry.sLower, E8TAxisProd0002Geometry.sUpper, E8TAxisProd0002Geometry.tLower, E8TAxisProd0002Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0002

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0003 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0003
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 4 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0003Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0003Geometry.rectangle, E8TAxisProd0003Geometry.sLower, E8TAxisProd0003Geometry.sUpper, E8TAxisProd0003Geometry.tLower, E8TAxisProd0003Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0003

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0004 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0004
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0004Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0004Geometry.rectangle, E8TAxisProd0004Geometry.sLower, E8TAxisProd0004Geometry.sUpper, E8TAxisProd0004Geometry.tLower, E8TAxisProd0004Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0004

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0005 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0005
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0005Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0005Geometry.rectangle, E8TAxisProd0005Geometry.sLower, E8TAxisProd0005Geometry.sUpper, E8TAxisProd0005Geometry.tLower, E8TAxisProd0005Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0005

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0006 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0006
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0006Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0006Geometry.rectangle, E8TAxisProd0006Geometry.sLower, E8TAxisProd0006Geometry.sUpper, E8TAxisProd0006Geometry.tLower, E8TAxisProd0006Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0006

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0007 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0007
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0007Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0007Geometry.rectangle, E8TAxisProd0007Geometry.sLower, E8TAxisProd0007Geometry.sUpper, E8TAxisProd0007Geometry.tLower, E8TAxisProd0007Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0007

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0008 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0008
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0008Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0008Geometry.rectangle, E8TAxisProd0008Geometry.sLower, E8TAxisProd0008Geometry.sUpper, E8TAxisProd0008Geometry.tLower, E8TAxisProd0008Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0008

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0009 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0009
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0009Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0009Geometry.rectangle, E8TAxisProd0009Geometry.sLower, E8TAxisProd0009Geometry.sUpper, E8TAxisProd0009Geometry.tLower, E8TAxisProd0009Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0009

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0010 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0010
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0010Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0010Geometry.rectangle, E8TAxisProd0010Geometry.sLower, E8TAxisProd0010Geometry.sUpper, E8TAxisProd0010Geometry.tLower, E8TAxisProd0010Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0010

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0011 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0011
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 4 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0011Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0011Geometry.rectangle, E8TAxisProd0011Geometry.sLower, E8TAxisProd0011Geometry.sUpper, E8TAxisProd0011Geometry.tLower, E8TAxisProd0011Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0011

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0012 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0012
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0012Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0012Geometry.rectangle, E8TAxisProd0012Geometry.sLower, E8TAxisProd0012Geometry.sUpper, E8TAxisProd0012Geometry.tLower, E8TAxisProd0012Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0012

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0013 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0013
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0013Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0013Geometry.rectangle, E8TAxisProd0013Geometry.sLower, E8TAxisProd0013Geometry.sUpper, E8TAxisProd0013Geometry.tLower, E8TAxisProd0013Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0013

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0014 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0014
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0014Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0014Geometry.rectangle, E8TAxisProd0014Geometry.sLower, E8TAxisProd0014Geometry.sUpper, E8TAxisProd0014Geometry.tLower, E8TAxisProd0014Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0014

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0015 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0015
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 32 : ℝ), (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0015Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0015Geometry.rectangle, E8TAxisProd0015Geometry.sLower, E8TAxisProd0015Geometry.sUpper, E8TAxisProd0015Geometry.tLower, E8TAxisProd0015Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0015

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0016 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0016
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5 / 32 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0016Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0016Geometry.rectangle, E8TAxisProd0016Geometry.sLower, E8TAxisProd0016Geometry.sUpper, E8TAxisProd0016Geometry.tLower, E8TAxisProd0016Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0016

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0017 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0017
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(5 / 32 : ℝ), (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0017Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0017Geometry.rectangle, E8TAxisProd0017Geometry.sLower, E8TAxisProd0017Geometry.sUpper, E8TAxisProd0017Geometry.tLower, E8TAxisProd0017Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0017

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0018 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0018
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (5 / 32 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0018Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0018Geometry.rectangle, E8TAxisProd0018Geometry.sLower, E8TAxisProd0018Geometry.sUpper, E8TAxisProd0018Geometry.tLower, E8TAxisProd0018Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0018

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0019 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0019
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0019Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0019Geometry.rectangle, E8TAxisProd0019Geometry.sLower, E8TAxisProd0019Geometry.sUpper, E8TAxisProd0019Geometry.tLower, E8TAxisProd0019Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0019

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0020 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0020
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 10 : ℝ), (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (1 / 50 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0020Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0020Geometry.rectangle, E8TAxisProd0020Geometry.sLower, E8TAxisProd0020Geometry.sUpper, E8TAxisProd0020Geometry.tLower, E8TAxisProd0020Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0020

end

-- ===== source module GeneralCK.Certificates.Generated.E8TAxisPositiveAggregation.Root0021 =====
section

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0021
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 10 : ℝ), (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  convert E8TAxisProd0021Certified.cellPositive using 1 <;>
    norm_num [E8TAxisProd0021Geometry.rectangle, E8TAxisProd0021Geometry.sLower, E8TAxisProd0021Geometry.sUpper, E8TAxisProd0021Geometry.tLower, E8TAxisProd0021Geometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0021

end


