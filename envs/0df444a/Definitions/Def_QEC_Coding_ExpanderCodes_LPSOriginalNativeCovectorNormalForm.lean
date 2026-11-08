-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:26:14.259837+00:00
-- url     : https://prove2.me/theorems/b380ae06-d203-4184-80ab-433bf3f1a194
-- title:
--   LPSOriginal Native Covector Normal Form
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Covector Normal Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
def lpsOriginalNormalizedFilledCovector
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun x => ContinuousLinearMap.mul ℂ ℂ
    (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
      (chartAt ℂ x x) (chartAt ℂ x x))
end
end QEC.Coding.TannerLiftedProduct


