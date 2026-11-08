-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:01:43.915756+00:00
-- url     : https://prove2.me/theorems/2163a3ba-797d-483a-b890-560504405b1d
-- title:
--   LPSOriginal Differential Images
-- statement:
--   Definitions and structural lemmas for LPSOriginal Differential Images, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialImages.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_openImmersion

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
local instance originalOverlapImageOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalSchemeOverlapMap N hpos b) :=
  lpsOriginalComplexNormalSchemeOverlapMap_openImmersion N hpos b
local instance originalChartImageOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos b) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos b
def lpsOriginalComplexNormalChartImage (b : Bool) :
    (lpsOriginalComplexNormalGluedScheme N hpos).Opens :=
  (lpsOriginalComplexNormalGluedChartMap N hpos b).opensRange
end
end QEC.Coding.TannerLiftedProduct


