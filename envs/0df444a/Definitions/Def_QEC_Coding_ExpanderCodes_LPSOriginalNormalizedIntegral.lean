-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:59:39.107201+00:00
-- url     : https://prove2.me/theorems/4d107826-9cd0-4b37-9758-33342c53c952
-- title:
--   LPSOriginal Normalized Integral
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalized Integral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizedIntegral.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
def lpsOriginalNormalizedFilledFunction (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) : LPSOriginalFilledCurve N → ℂ :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  chartNormalizedMeromorphicFunction F
lemma lpsOriginalNormalizedFilledFunction_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic N hN (lpsOriginalNormalizedFilledFunction N hN F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact chartNormalizedMeromorphicFunction_meromorphic F hF
end
end QEC.Coding.TannerLiftedProduct


