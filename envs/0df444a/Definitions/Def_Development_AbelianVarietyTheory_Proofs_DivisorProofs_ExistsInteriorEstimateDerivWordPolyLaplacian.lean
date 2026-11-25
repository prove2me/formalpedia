-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInteriorEstimateDerivWordPolyLaplacian
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInteriorEstimateDerivWordPolyLaplacian
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:55.428313+00:00
-- url     : https://prove2.me/theorems/f498f8ca-8c23-5540-a382-e1310df04d93
-- title:
--   Exists Interior Estimate Deriv Word Poly Laplacian
-- statement:
--   Definitions and structural lemmas for Exists Interior Estimate Deriv Word Poly Laplacian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInteriorEstimateDerivWordPolyLaplacian.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold
namespace GlobalTheory
open ZetaZeros.D.EllReg GlobalTheory.HCA
end GlobalTheory


