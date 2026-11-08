-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:21:29.249933+00:00
-- url     : https://prove2.me/theorems/c0df6271-36a6-464f-9670-d35710c2d344
-- title:
--   LPSOriginal Native Covector Coordinates
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Covector Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorCoordinates.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
end
end QEC.Coding.TannerLiftedProduct


