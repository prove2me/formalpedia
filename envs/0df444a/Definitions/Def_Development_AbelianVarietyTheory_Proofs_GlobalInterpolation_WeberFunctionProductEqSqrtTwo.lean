-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:04.999632+00:00
-- url     : https://prove2.me/theorems/3fa9f0ce-d72e-4c3d-b2b6-98f8336d657c
-- title:
--   Weber Function Product Eq Sqrt Two
-- statement:
--   Definitions and structural lemmas for Weber Function Product Eq Sqrt Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionProductEqSqrtTwo.lean

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
noncomputable section
namespace GlobalTheory.WeberProduct
def eulerProd (x : ℂ) : ℂ := ∏' n : ℕ, (1 - x ^ (n + 1))
def oddProd (x : ℂ) : ℂ := ∏' k : ℕ, (1 - x ^ (2 * k + 1))
end GlobalTheory.WeberProduct


