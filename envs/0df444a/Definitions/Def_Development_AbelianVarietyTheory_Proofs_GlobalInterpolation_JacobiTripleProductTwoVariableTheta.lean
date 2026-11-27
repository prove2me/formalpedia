-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductTwoVariableTheta
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductTwoVariableTheta
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:44:37.12647+00:00
-- url     : https://prove2.me/theorems/808e5ae3-decf-4974-b1f4-568bf9f93da7
-- title:
--   Jacobi Triple Product Two Variable Theta
-- statement:
--   Definitions and structural lemmas for Jacobi Triple Product Two Variable Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleProductTwoVariableTheta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductLimitStatement
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
noncomputable section
namespace GlobalTheory.JacobiTriple
end GlobalTheory.JacobiTriple


