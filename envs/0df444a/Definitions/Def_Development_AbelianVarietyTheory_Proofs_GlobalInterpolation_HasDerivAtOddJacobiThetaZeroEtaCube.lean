-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:17.281365+00:00
-- url     : https://prove2.me/theorems/f2c7c92d-7279-42be-81b1-31221946fd88
-- title:
--   Has Deriv At Odd Jacobi Theta Zero Eta Cube
-- statement:
--   Definitions and structural lemmas for Has Deriv At Odd Jacobi Theta Zero Eta Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCube.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
def tailProd (τ : ℍ) (v : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ) * v)
end GlobalTheory.ThetaWeberRoad.OddDeriv
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
end GlobalTheory.ThetaWeberRoad.OddDeriv


